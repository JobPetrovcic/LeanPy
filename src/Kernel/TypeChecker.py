from typing import List, Optional, Sequence, Tuple

from typeguard import typechecked
from Kernel.Analysis import has_fvar_not_in_context, print_neg
from Kernel.Cache.EquivManager import EquivManager
from Kernel.Cache.Cache import InferCache, WHNFCache
from Structures.Environment.Declaration.Declaration import Axiom, Constructor, Declaration, DeclarationInfo, Definition, InductiveType, Opaque, Quot, Recursor, Theorem, compare_reducibility_hints
from Structures.Environment.Declaration.DeclarationManipulation import is_structural_inductive
from Structures.Environment.Environment import Environment
from Structures.Environment.LocalContext import LocalContext
from Structures.Environment.NatReduction import *
from Structures.Environment.NatReduction import nat_lit_to_constructor
from Structures.Environment.NatReduction import str_lit_to_constructor
from Structures.Environment.NatReduction import reduce_bin_nat_pred
from Structures.Expression.Expression import *
from Structures.Expression.ExpressionManipulation import ReductionStatus, abstract_bvar, abstract_multiple_bvar, fold_apps, has_fvar, has_loose_bvars, has_specific_fvar, instantiate_bvar, instantiate_bvars, level_zip, substitute_level_params_in_expression, unfold_app, get_app_function
from Structures.Expression.Level import *
from Structures.Expression.LevelManipulation import is_equivalent, is_equivalent_list, are_unique_level_params
from Kernel.KernelErrors import ExpectedDifferentExpressionError, ExpectedDifferentTypesError, PanicError, ProjectionError, EnvironmentError, DeclarationError, RecursorError
from Structures.Name import Name
import warnings

import sys
sys.setrecursionlimit(10**4)

#TODO:
# - special cases for Nat and String literals

class TypeChecker:
    def __init__(self, allow_loose_infer : bool = False):
        self.allow_loose_infer = allow_loose_infer

        self.whnf_cache = WHNFCache()
        self.whnf_core_cache = WHNFCache()
        self.infer_cache = [InferCache(), InferCache()]

        self.equiv_manager = EquivManager()

        self.environment = Environment()
        self.local_context = LocalContext()

    # LOCAL CONTEXT INTERACTIONS
    @typechecked
    #@profile
    def remove_fvar(self, fvar: FVar):
        self.local_context.remove_fvar(fvar)
    
    @typechecked
    #@profile
    def get_type_of_fvar(self, fvar : FVar) -> Expression:
        return self.local_context.get_fvar_type(fvar)
    
    @typechecked
    #@profile
    def get_value_of_fvar(self, fvar : FVar) -> Optional[Expression]:
        return self.local_context.get_fvar_value(fvar)
    
    @typechecked
    #@profile
    def instantiate(self, body : Expression, val : Expression) -> Expression:
        """
        Replace the outermost bound variable in the body with the value. Clones the body(!).
        """
        return instantiate_bvar(body, val)
    
    @typechecked
    #@profile
    def instantiate_multiple(self, body : Expression, vals : Sequence[Expression]) -> Expression:
        """
        Replace the outermost bound variables in the body with the values. Clones the body(!).
        IMPORTANT: vals should be in order of the innermost bound variable to the outermost bound variable.
        """
        return instantiate_bvars(body, vals)
    
    @typechecked
    #@profile
    def create_fvar(self, name: Name, type: Expression, val : Optional[Expression], is_let : bool) -> FVar:
        fvar = FVar(name, type, val, is_let=is_let)
        self.local_context.add_fvar(fvar)
        return fvar

    @typechecked
    #@profile
    def instantiate_fvar(
            self, 
            bname : Name, 
            arg_type : Expression, # the type of the fvar
            arg_val : Optional[Expression],  # the value of the fvar
            body : Expression, # the body in which the fvar is instantiated
            is_let : bool = False
        ) -> Tuple[FVar, Expression]: # CHECKED
        fvar = self.create_fvar(bname, arg_type, arg_val, is_let=is_let)
        return fvar, self.instantiate(body, fvar)
    
    @typechecked
    #@profile
    def instantiate_fvar_multiple_bodies(
            self, 
            bname : Name, 
            arg_type : Expression, # the type of the fvar
            arg_val : Optional[Expression], # the value of the fvar
            bodies : List[Expression], # the bodies in which the fvar is instantiated
            is_let : bool = False) -> Tuple[FVar, List[Expression]]:
        fvar = self.create_fvar(bname, arg_type, arg_val, is_let=is_let)
        return fvar, [self.instantiate(body, fvar) for body in bodies]
    
    @typechecked
    #@profile
    def abstract(self, fvar : FVar, expr : Expression) -> Expression: # CHECKED
        """Abstracts the outermost bound variable in the given expression."""
        # remove the fvar from the local context
        self.remove_fvar(fvar)
        abstract_expression = abstract_bvar(expr, fvar)
        return abstract_expression
    
    # HELPERS
    @typechecked
    #@profile
    def ensure_pi(self, expr : Expression) -> Pi: # CHECKED
        if isinstance(expr, Pi): 
            return expr
        
        expr = self.whnf(expr)
        if  isinstance(expr, Pi): return expr
        else: raise ExpectedDifferentExpressionError(Pi, expr.__class__)

    @typechecked
    #@profile
    def is_structure_like(self, decl_name : Name) -> bool:
        decl = self.environment.get_declaration_under_name(decl_name)
        if not isinstance(decl, InductiveType): return False
        return is_structural_inductive(decl) and decl.num_indices == 0 and not decl.is_recursive
    
    @typechecked
    #@profile
    def is_prop(self, e : Expression):
        inferred_type = self.whnf(self.infer_core(e, infer_only=(self.allow_loose_infer and True)))
        return isinstance(inferred_type, Sort) and is_equivalent(inferred_type.level, self.environment.level_zero)

    # DEFINITIONAL EQUALITY
    @typechecked
    #@profile
    def def_eq_sort(self, l : Sort, r : Sort) -> bool:
        """Sorts are equal if their levels satisfy antisymmetry.
        The comparsion function does not change anything, so def_eq_sort is safe to use when passing by reference.
        """
        return is_equivalent(l.level, r.level)

    @typechecked
    #@profile
    def def_eq_const(self, l : Const, r : Const) -> bool:
        """
        If the names are the same, and the level parameters are equal, then the constants are equal.
        Since nothing is changed, this function is safe to use when passing by reference.
        """
        if l.name == r.name:
            if is_equivalent_list(l.lvl_params, r.lvl_params): return True
            else: warnings.warn(f"Constants {l} and {r} have the same name but different level parameters : {[str(lvl) for lvl in l.lvl_params]} and {[str(lvl) for lvl in r.lvl_params]}")
        return False

    @typechecked
    #@profile
    def def_eq_app(self, l : App, r : App) -> bool:
        f_fn, f_args = unfold_app(l.fn)
        g_fn, g_args = unfold_app(r.fn)
        if not self.def_eq(f_fn, g_fn):
            return False
        
        if len(f_args) != len(g_args): return False
        for f_arg, g_arg in zip(f_args, g_args):
            if not self.def_eq(f_arg, g_arg):
                return False
        return True

    @typechecked
    #@profile
    def def_eq_pi(self, l: Pi, r: Pi) -> bool:
        if not self.def_eq(l.arg_type, r.arg_type):
            return False
        
        fvar, (l_n, r_n) = self.instantiate_fvar_multiple_bodies(
            bname=l.bname, 
            arg_type=l.arg_type, 
            arg_val=None, 
            bodies=[l.body_type, r.body_type]
        )

        result = self.def_eq(l_n, r_n) 
        self.remove_fvar(fvar)
        return result

    @typechecked
    #@profile
    def def_eq_lambda(self, l : Lambda, r : Lambda) -> bool:
        if not self.def_eq(l.arg_type, r.arg_type):
            return False
        
        fvar, (l_n, r_n) = self.instantiate_fvar_multiple_bodies(
            bname=l.bname, 
            arg_type=l.arg_type, 
            arg_val=None,
            bodies=[l.body, r.body], 
        )
        ret = self.def_eq(l_n, r_n)
        self.remove_fvar(fvar)
        return ret

    @typechecked
    #@profile
    def try_structural_eta_expansion_core(self, t : Expression, s : Expression) -> bool: # CHECKED
        # First part: deconstruct s, ensure it is an application of a constructor
        s_fn, s_args = unfold_app(s)

        if not isinstance(s_fn, Const): return False
        
        decl = self.environment.get_declaration_under_name(s_fn.name)
        if not isinstance(decl, Constructor): return False

        # Second part: ensure that the application has the correct number of arguments and that the inductive type is a structure
        if len(s_args) != decl.num_params + decl.num_fields: return False
        if not self.is_structure_like(decl.inductive_name): return False

        # Third part: ensure that the types are equal
        if not self.def_eq(
            self.infer_core(t, infer_only=(self.allow_loose_infer and True)),
            self.infer_core(s, infer_only=(self.allow_loose_infer and True)),
        ): return False

        # Fourth part: ensure that the arguments are equal:
        # s was decomposed, so we know the arguments
        # for t we don't know the arguments, so we use proj to get them
        for i in range(decl.num_params, len(s_args)):
            t_i_proj = Proj(type_name=decl.inductive_name, index=i-decl.num_params, struct=t)

            # compare the arguments
            if not self.def_eq(t_i_proj, s_args[i]): return False
        return True

    @typechecked
    #@profile
    def try_structural_eta_expansion(self, l : Expression, r : Expression) -> bool:
        return self.try_structural_eta_expansion_core(l, r) or self.try_structural_eta_expansion_core(r, l)
    
    @typechecked
    #@profile
    def try_eta_expansion_core(self, t : Expression, s : Expression) -> bool:
        """
        Tries to eta expand s: if s is a function, then by eta expansion, it is equal to the expression "fun x => s x".
        Always assumes that t and s were cloned beforehand.
        """
        if not (isinstance(t, Lambda) and (not isinstance(s, Lambda))): 
            return False
        
        s_type = self.whnf(self.infer_core(s, infer_only=(self.allow_loose_infer and False)))
        if not isinstance(s_type, Pi): 
            return False
        new_s = Lambda(bname=s_type.bname, arg_type=s_type.arg_type, body=App(s, BVar(0)))
        return self.def_eq(t, new_s)

    @typechecked
    #@profile
    def try_eta_expansion(self, t : Expression, s : Expression) -> bool:
        """
        Tries to eta expand y and compares it to x, then tries to eta expand x and compares it to y.
        Always assumes that x and y were cloned beforehand.
        """
        return self.try_eta_expansion_core(t, s) or self.try_eta_expansion_core(s, t)
    
    @typechecked
    #@profile
    def def_eq_easy(self, l: Expression, r: Expression) -> Optional[bool]:
        if self.equiv_manager.were_found_and_equiv(l, r): return True

        if isinstance(l, Sort) and isinstance(r, Sort): return self.def_eq_sort(l, r)
        elif isinstance(l, BVar) or isinstance(r, BVar): raise PanicError("BVar should have been substituted by now, when comparing expressions for definitional equality.")
        elif isinstance(l, FVar) and isinstance(r, FVar): return l is r
        
        elif isinstance(l, Pi) and isinstance(r, Pi):
            return self.def_eq_pi(l, r)
        elif isinstance(l, Lambda) and isinstance(r, Lambda):
            return self.def_eq_lambda(l, r)
        elif isinstance(l, NatLit) and isinstance(r, NatLit): return l.val == r.val
        elif isinstance(l, StringLit) and isinstance(r, StringLit): return l.val == r.val
    
    @typechecked
    #@profile
    def def_eq_proof_irrel(self, t : Expression, s : Expression) -> Optional[bool]:
        """ Proof irrelevance support for propositions. If two expressions have equal types, and the types are proposition, then the expressions are considered equal. """
        t_type = self.infer_core(t, infer_only=(self.allow_loose_infer and True))
        if not self.is_prop(t_type):
            return None
        s_type = self.infer_core(s, infer_only=(self.allow_loose_infer and True))
        return self.def_eq(t_type, s_type)
    
    @typechecked
    #@profile
    def def_eq_unit_like(self, t : Expression, s : Expression) -> bool:
        t_type = self.whnf(self.infer_core(t, infer_only=(self.allow_loose_infer and True)))
        inductive_const = get_app_function(t_type)

        if not isinstance(inductive_const, Const): return False
        if not self.is_structure_like(inductive_const.name): return False

        constructor = self.get_first_constructor(inductive_const.name)
        if constructor is None: return False
        if constructor.num_fields != 0: return False
        return self.def_eq_core(t_type, self.infer_core(s, infer_only=(self.allow_loose_infer and True)))
    
    @print_neg
    @typechecked
    #@profile
    def def_eq_core(self, l: Expression, r: Expression) -> bool:
        if l is r: return True

        # TODO might need to optimize has_fvar by caching
        if not has_fvar(l) and isinstance(r, Const) and r.name == self.environment.Bool_true_name:
            whnfd_l = self.whnf(l)
            if isinstance(whnfd_l, Const) and whnfd_l.name == self.environment.Bool_true_name:
                return True
        
        is_easy = self.def_eq_easy(l, r)
        if is_easy is not None: return is_easy

        if isinstance(l, Const) and isinstance(r, Const):
            if self.def_eq_const(l, r): return True

        l_n = self.whnf_core(l, cheap_rec=False, cheap_proj=True)
        r_n = self.whnf_core(r, cheap_rec=False, cheap_proj=True)
     
        if (l_n is not l) or (r_n is not r):
            is_easy = self.def_eq_easy(l_n, r_n)
            if is_easy is not None: return is_easy

        is_proof_irr = self.def_eq_proof_irrel(l_n, r_n)
        if is_proof_irr is not None: return is_proof_irr

        l_n_n, r_n_n, try_lazy = self.lazy_delta_reduction(l_n, r_n)
        if try_lazy is not None: return try_lazy

        if isinstance(l_n_n, Const) and isinstance(r_n_n, Const):
            if self.def_eq_const(l_n_n, r_n_n): return True
        if isinstance(l_n_n, FVar) and isinstance(r_n_n, FVar) and (l_n_n is r_n_n): return True
        if isinstance(l_n_n, Proj) and isinstance(r_n_n, Proj) and l_n_n.index == r_n_n.index:
            if self.lazy_delta_proj_reduction(l_n_n.struct, r_n_n.struct, l_n_n.index): return True

        l_n_n_n = self.whnf_core(l_n_n, cheap_rec=False, cheap_proj=False) # don't use cheap_proj now
        r_n_n_n = self.whnf_core(r_n_n, cheap_rec=False, cheap_proj=False) # don't use cheap_proj now

        if (l_n_n_n is not l_n_n) or (r_n_n_n is not r_n_n): return self.def_eq_core(l_n_n_n, r_n_n_n)
#
        is_easy = self.def_eq_easy(l_n_n_n, r_n_n_n)
        if is_easy is not None: return is_easy
#
        if isinstance(l_n_n_n, App) and isinstance(r_n_n_n, App):
            if self.def_eq_app(l_n_n_n, r_n_n_n): return True

        # Reductions

        if self.try_eta_expansion(l_n_n_n, r_n_n_n):
            return True
        if self.try_structural_eta_expansion(l_n_n_n, r_n_n_n):
            return True
        #
        ##r = try_string_lit_expansion(t_n, s_n); TODO
        ##if (r != l_undef) return r == l_true;
   #
        if self.def_eq_unit_like(l_n_n_n, r_n_n_n): return True

        return False
    
    def def_eq(self, l: Expression, r: Expression) -> bool:
        ret = self.def_eq_core(l, r)
        if ret: self.equiv_manager.add_equiv(l, r)
        return ret
    
    # REDUCTIONS
    @typechecked
    #@profile
    def beta_reduction(self, 
            f : Expression, #  ( ... ((f a_1) a_2) ... a_n -> f, [a_1, a_2, ..., a_n] outermost to innermost
            args : List[Expression]
        ) -> Expression:
        """
        Reduces the application by substituting the argument in the body.
        """
        n_successful_subs = 0
        while isinstance(f, Lambda) and n_successful_subs < len(args):
            f = f.body
            n_successful_subs += 1
        
        # reverse the successful_args, because we pass the args to instantiate_multiple in the innermost to outermost order
        rest_args = args[n_successful_subs:]
        successful_args = args[:n_successful_subs][::-1]
        
        inst_f = self.instantiate_multiple(f, successful_args)

        return fold_apps(inst_f, rest_args)
    
    @typechecked
    #@profile
    def is_delta(self, expr : Expression) -> Optional[Tuple[Const, Definition | Opaque | Theorem, List[Expression]]]:
        """Checks if the expression is delta reducible: if it is an application of a declaration, then it returns the declaration and the arguments. Otherwise, it returns None."""
        fn, args = unfold_app(expr)
        #print(f"checking if {fn} is a delta")
        if not isinstance(fn, Const): return None
        #print(f"{fn} is a const")
        decl = self.environment.get_declaration_under_name(fn.name)
        #print(f"{fn} is a declaration")
        if not decl.has_value(): return None
        #print(f"{fn} has a value")
        assert isinstance(decl, Definition) or isinstance(decl, Opaque) or isinstance(decl, Theorem)
        return fn, decl, args

    @typechecked
    #@profile
    def delta_reduction_core(self, fn : Const, decl : Definition | Opaque | Theorem, args : List[Expression]) -> Expression:
        assert fn.name == decl.info.name
        decl_val = self.environment.get_declaration_val_with_substituted_level_params(decl, fn.lvl_params)
        return fold_apps(decl_val, args)

    @typechecked
    #@profile
    def delta_reduction(self, expr : Expression) -> Optional[Expression]:
        """ Unfolds the applications of the expression. If the function is a declaration, then it unfolds it. """
        #print(f"delta reducing {expr}")
        is_d = self.is_delta(expr)
        #print(f"expr {expr} is a delta")
        if is_d is None: return None
        ret = self.delta_reduction_core(*is_d)
        #print(f"delta reduced {expr} to {ret}")
        return ret
    
    @typechecked
    #@profile
    def reduce_proj_core(self, proj_struct : Expression, idx : int) -> Optional[Expression]:
        """ If we have a projection of an expression that is an application of a constructor, then we reduce it to the corresponding argument of the constructor. 
        
        For example, proj 0 (Prod.mk (A) (B) (a : A) (b : B)) would be reduced to a. Note that in this case A B are parameters of the constructor, and a and b are the actual arguments, used in the projection.
        """
        if isinstance(proj_struct, StringLit): proj_struct = str_lit_to_constructor(self.environment, proj_struct)
        
        proj_struct_fn, proj_struct_args = unfold_app(proj_struct)
        if not isinstance(proj_struct_fn, Const): return None
        constructor_decl = self.environment.get_declaration_under_name(proj_struct_fn.name)
        if not isinstance(constructor_decl, Constructor): return None

        if constructor_decl.num_params + idx >= len(proj_struct_args): return None

        return proj_struct_args[constructor_decl.num_params + idx]
    
    @typechecked
    #@profile
    def reduce_proj(self, proj : Proj, cheap_rec :bool, cheap_proj : bool) -> Optional[Expression]:
        idx = proj.index
        c = proj.struct
        # use whnf to unfold the definitions if cheap_proj is False
        c = self.whnf_core(c, cheap_rec=cheap_rec, cheap_proj=cheap_proj) if cheap_proj else self.whnf(c) 
        return self.reduce_proj_core(c, idx)
    
    @typechecked
    #@profile
    def try_unfold_proj_app(self, e : Expression) -> Optional[Expression]: 
        f = get_app_function(e)
        if not isinstance(f, Proj): return None
        e_new = self.whnf_core(e, cheap_rec=False, cheap_proj=False)
        if e_new is e: return None
        return e_new

    ##@profile
    @typechecked
    #@profile
    def lazy_delta_reduction_step(self, t_n : Expression, s_n : Expression) -> Tuple[Expression, Expression, ReductionStatus]:
        id_t = self.is_delta(t_n)
        id_s = self.is_delta(s_n)

        if (id_t is None) and (id_s is None):             
            return t_n, s_n, ReductionStatus.UNKNOWN
        elif (id_t is not None) and (id_s is None):
            s_new = self.try_unfold_proj_app(s_n)
            if s_new is not None: s_n = s_new
            else: t_n = self.whnf_core(self.delta_reduction_core(*id_t), cheap_rec=False, cheap_proj=True)
        elif (id_t is None) and (id_s is not None):
            t_new = self.try_unfold_proj_app(t_n)
            if t_new is not None: 
                #print(f"unfolding proj {t_n}")
                t_n = t_new
            else: 
                #print(f"delta reducing {s_n}")
                s_n = self.whnf_core(self.delta_reduction_core(*id_s), cheap_rec=False, cheap_proj=True)
        elif (id_t is not None) and (id_s is not None):
            hint_compare = compare_reducibility_hints(id_t[1], id_s[1])
            if hint_compare < 0: # reduce t
                #print(f"delta reducing hint {t_n}")
                t_n = self.whnf_core(self.delta_reduction_core(*id_t), cheap_rec=False, cheap_proj=True)
            elif hint_compare > 0: # reduce s
                #print(f"delta reducing hint {s_n}")
                s_n = self.whnf_core(self.delta_reduction_core(*id_s), cheap_rec=False, cheap_proj=True)
            else: # reduce both
                #print(f"delta reducing both {t_n} and {s_n}")
                t_n = self.whnf_core(self.delta_reduction_core(*id_t), cheap_rec=False, cheap_proj=True)
                s_n = self.whnf_core(self.delta_reduction_core(*id_s), cheap_rec=False, cheap_proj=True)
        else:
            raise PanicError("Unreachable code reached in lazy_delta_reduction_step.")

        is_easy = self.def_eq_easy(t_n, s_n)
        if is_easy is not None:
            return t_n, s_n, (ReductionStatus.EQUAL if is_easy else ReductionStatus.NOT_EQUAL)
        else: return t_n, s_n, ReductionStatus.CONTINUE
    
    ##@profile
    @typechecked
    #@profile
    def lazy_delta_reduction(self, t_n : Expression, s_n : Expression) -> Tuple[Expression, Expression, Optional[bool]]:
        while True:
            if not has_fvar(t_n) and not has_fvar(s_n): # TODO: this should be optimized by using a counter for fvars
                nat_t = self.reduce_nat_lit(t_n) 
                if nat_t is not None: 
                    return t_n, s_n, self.def_eq_core(nat_t, s_n)
                nat_s = self.reduce_nat_lit(s_n)
                if nat_s is not None: 
                    return t_n, s_n, self.def_eq_core(t_n, nat_s)
            
            native_t = self.reduce_native(t_n)
            if native_t is not None:
                return t_n, s_n, self.def_eq_core(native_t, s_n)
            native_s = self.reduce_native(s_n)
            if native_s is not None:
                return t_n, s_n, self.def_eq_core(t_n, native_s)

            t_n, s_n, status = self.lazy_delta_reduction_step(t_n, s_n)

            if status == ReductionStatus.CONTINUE: continue
            elif status == ReductionStatus.EQUAL: return t_n, s_n, True
            elif status == ReductionStatus.NOT_EQUAL: return t_n, s_n, False
            elif status == ReductionStatus.UNKNOWN: return t_n, s_n, None
            else: raise PanicError("Unknown reduction status.")

    @typechecked
    #@profile
    def lazy_delta_proj_reduction(self, t_n : Expression, s_n : Expression, idx : int) -> bool:
        while True:
            t_n, s_n, status = self.lazy_delta_reduction_step(t_n, s_n)
            if status is ReductionStatus.CONTINUE: continue
            elif status is ReductionStatus.EQUAL: return True
            else:
                t = self.reduce_proj_core(t_n, idx)
                if t is not None:
                    s = self.reduce_proj_core(s_n, idx)
                    if s is not None:
                        return self.def_eq_core(t, s)
                return self.def_eq_core(t_n, s_n)

    @typechecked
    #@profile
    def reduce_nat_lit(self, e : Expression) -> Optional[Expression]:
        if has_fvar(e): return None
        
        fn, args = unfold_app(e)
        if not isinstance(fn, Const): return None
        if len(args) == 0: # TODO: why does not lean kernel do this?
            if fn.name == self.environment.Nat_zero_name: return NatLit(0)
        if len(args) == 1:
            if fn.name == self.environment.Nat_succ_name:
                arg = self.whnf(args[0])
                if isinstance(arg, NatLit): return NatLit(arg.val + 1)
                if isinstance(arg, Const) and arg.name == self.environment.Nat_zero_name: return NatLit(1)
                return None
        if len(args) == 2:
            arg1 = self.whnf(args[0])
            if not isinstance(arg1, NatLit): return None
            arg2 = self.whnf(args[1])
            if not isinstance(arg2, NatLit): return None
            
            name = fn.name
            if name == self.environment.Nat_add_name: return reduce_bin_nat_op(nat_add, arg1.val, arg2.val)
            elif name == self.environment.Nat_sub_name: return reduce_bin_nat_op(nat_sub, arg1.val, arg2.val)
            elif name == self.environment.Nat_mul_name: return reduce_bin_nat_op(nat_mul, arg1.val, arg2.val)
            elif name == self.environment.Nat_pow_name: return reduce_bin_nat_op(nat_pow, arg1.val, arg2.val)
            elif name == self.environment.Nat_gcd_name: return reduce_bin_nat_op(nat_gcd, arg1.val, arg2.val)
            elif name == self.environment.Nat_mod_name: return reduce_bin_nat_op(nat_mod, arg1.val, arg2.val)
            elif name == self.environment.Nat_div_name: return reduce_bin_nat_op(nat_div, arg1.val, arg2.val)
            elif name == self.environment.Nat_eq_name: return reduce_bin_nat_pred(self.environment, nat_beq, arg1.val, arg2.val)
            elif name == self.environment.Nat_le_name: return reduce_bin_nat_pred(self.environment,nat_ble, arg1.val, arg2.val)
            elif name == self.environment.Nat_land_name: return reduce_bin_nat_op(nat_land, arg1.val, arg2.val)
            elif name == self.environment.Nat_lor_name: return reduce_bin_nat_op(nat_lor, arg1.val, arg2.val)
            elif name == self.environment.Nat_lxor_name: return reduce_bin_nat_op(nat_xor, arg1.val, arg2.val)
            elif name == self.environment.Nat_shiftl_name: return reduce_bin_nat_op(nat_shiftl, arg1.val, arg2.val)
            elif name == self.environment.Nat_shiftr_name: return reduce_bin_nat_op(nat_shiftr, arg1.val, arg2.val)
        return None

    def reduce_native(self, e : Expression) -> Optional[Expression]:
        if not isinstance(e, App): return None
        if not isinstance(e.arg, Const): return None
        if isinstance(e.fn, Const) and e.fn.name == self.environment.Bool_reduce_name:
            raise NotImplementedError("TODO")
            #object * r = ir::run_boxed(env, options(), const_name(arg), 0, nullptr);
            #if (!lean_is_scalar(r)) {
            #    lean_dec_ref(r);
            #    throw kernel_exception(env, "type checker failure, unexpected result value for 'Lean.reduceBool'");
            #}
            #return lean_unbox(r) == 0 ? some_expr(mk_bool_false()) : some_expr(mk_bool_true());
        if isinstance(e.fn, Const) and e.fn.name == self.environment.Nat_reduce_name:
            raise NotImplementedError("TODO")
            #object * r = ir::run_boxed(env, options(), const_name(arg), 0, nullptr);
            #if (lean_is_scalar(r) || lean_is_mpz(r)) {
            #    return some_expr(mk_lit(literal(nat(r))));
            #} else {
            #    throw kernel_exception(env, "type checker failure, unexpected result value for 'Lean.reduceNat'");
            #}

    # INDUCTIVE
    @typechecked
    #@profile
    def get_first_constructor(self, inductive_name : Name) -> Optional[Constructor]:
        decl = self.environment.get_declaration_under_name(inductive_name)
        if not isinstance(decl, InductiveType): return None
        if decl.number_of_constructors() == 0: return None
        return self.environment.get_constructor(decl.constructor_names[0])
    
    @typechecked
    #@profile
    def expand_eta_struct(self, e_type : Expression, e : Expression):
        fn, args = unfold_app(e_type)
        if not isinstance(fn, Const): return e

        constructor = self.get_first_constructor(fn.name)
        if not constructor: return e

        assert len(args) >= constructor.num_params
        args = args[:constructor.num_params]
        result = fold_apps(Const(name=constructor.info.name, lvl_params=fn.lvl_params), args)
        result = fold_apps(result, [Proj(type_name=fn.name, index=i, struct=e) for i in range(constructor.num_fields)])
        return result
    
    # inductive stuff
    @typechecked
    #@profile
    def to_constructor_when_structure(self, inductive_name : Name, e : Expression) -> Expression:
        if not self.is_structure_like(inductive_name): return e
        f = get_app_function(e)
        if isinstance(f, Const) and isinstance(self.environment.get_declaration_under_name(f.name), Constructor): return e

        e_type = self.whnf(self.infer_core(e, infer_only=(self.allow_loose_infer and True))) # TODO: cheap_rec

        e_type_fn = get_app_function(e_type)
        if not (isinstance(e_type_fn, Const) and e_type_fn.name == inductive_name): return e 

        if self.is_prop(e_type): return e
        return self.expand_eta_struct(e_type, e)
    
    # inductive stuff
    @typechecked
    #@profile
    def mk_nullary_constructor(self, type_e : Expression, num_params : int) -> Optional[Expression]:
        d, args = unfold_app(type_e)
        if not isinstance(d, Const): return None
        constructor = self.get_first_constructor(d.name)
        if constructor is None: return None
        args = args[:num_params]
        return fold_apps(Const(name=constructor.info.name, lvl_params=d.lvl_params), args)

    @typechecked
    #@profile
    def to_constructor_when_K(self, recursor : Recursor, e : Expression, cheap_rec : bool, cheap_proj : bool) -> Expression:
        """See https://stackoverflow.com/questions/39239363/what-is-axiom-k
        For datatypes that support K-axiom, given `e` an element of that type, we convert (if possible)
        to the default constructor. For example, if `e : a = a`, then this method returns `eq.refl a` """
        assert recursor.isK, "Cannot apply K-axiom to a recursor that is not K."
        app_type = self.infer_core(e, infer_only=(self.allow_loose_infer and True))
        app_type = self.whnf_core(app_type, cheap_rec=cheap_rec, cheap_proj=cheap_proj) if cheap_rec else self.whnf(app_type)
        app_type_inductive, _ = unfold_app(app_type)

        if not isinstance(app_type_inductive, Const): return e
        if app_type_inductive.name != recursor.get_major_induct(): return e # type incorrect

        new_constructor_app = self.mk_nullary_constructor(app_type, recursor.num_params)
        if not new_constructor_app: return e
        new_type = self.infer_core(new_constructor_app, infer_only=(self.allow_loose_infer and True))

        if not self.def_eq(app_type, new_type): return e
        return new_constructor_app
    
    # QUOTIENT
    @typechecked
    #@profile
    def quot_reduce_rec(self, e : Expression) -> Optional[Expression]:
        fn, args = unfold_app(e)
        if not isinstance(fn, Const): return None
        mk_pos = 0 # the position of the Quot r argument
        arg_pos = 0 # the position of the 
        if fn.name == self.environment.Quot_lift_name:
            #assert not self.environment.exists_declaration_under_name(fn.name)
            mk_pos = 5
            arg_pos = 3
        elif fn.name == self.environment.Quot_ind_name:
            #assert not self.environment.exists_declaration_under_name(fn.name)
            mk_pos = 4
            arg_pos = 3
        else: return None

        if len(args) <= mk_pos: return None
        mk = self.whnf(args[mk_pos]) # whnf to expose the Quot_mk
        #print(self.local_context)

        assert isinstance(mk, App)
        mk_fn, mk_args = unfold_app(mk)

        if not isinstance(mk_fn, Const): return None
        if mk_fn.name != self.environment.Quot_mk_name: return None
        if len(mk_args) != 3: return None # the Quot.mk takes 3 arguments

        f = args[arg_pos] # get the function we are lifting/inducing
        r = App(f, mk.arg) # get the class representative and apply f on it

        elim_arity = mk_pos+1
        if len(args) > elim_arity:
            r = fold_apps(r, args[elim_arity:]) # reapply the arguments that were not relevant for the recursor
        return r

    @typechecked
    #@profile
    def reduce_recursor(self, e : Expression, cheap_rec : bool, cheap_proj : bool) -> Optional[Expression]:
        # First check if it is a quotient recursor and can be reduced
        r = self.quot_reduce_rec(e)
        if r is not None:
            assert self.def_eq(self.infer_core(e, infer_only=False), self.infer_core(r, infer_only=False))
            return r

        # Second unfold the application and get the recursor
        rec_fn, rec_args = unfold_app(e)
        if not isinstance(rec_fn, Const): return None
        
        rec_decl = self.environment.get_declaration_under_name(rec_fn.name)
        if not isinstance(rec_decl, Recursor): return None

        major_index = rec_decl.get_major_index()

        if major_index >= len(rec_args): return None
        major = rec_args[major_index]

        if rec_decl.isK:
            major = self.to_constructor_when_K(rec_decl, major, cheap_rec=cheap_rec, cheap_proj=cheap_proj) # TODO cheap_rec

        major = self.whnf_core(major, cheap_rec=cheap_rec, cheap_proj=cheap_proj) if cheap_rec else self.whnf(major) 
        if isinstance(major, NatLit):
            major = nat_lit_to_constructor(self.environment, major)
        elif isinstance(major, StringLit):
            major = str_lit_to_constructor(self.environment, major)
        else:
            major = self.to_constructor_when_structure(rec_decl.get_major_induct(), major)
        
        rule = rec_decl.get_recursion_rule(major)
        if rule is None: return None

        _, major_args = unfold_app(major)
        if len(major_args) < rule.num_fields: return None 
        if len(rec_fn.lvl_params) != len(rec_decl.info.lvl_params): return None
        rhs = substitute_level_params_in_expression(rule.value, level_zip(rec_decl.info.lvl_params, rec_fn.lvl_params)) # clones the rule.value

        # apply parameters, motives and minor premises from recursor application.
        rhs = fold_apps(rhs, rec_args[:rec_decl.num_params + rec_decl.num_motives + rec_decl.num_minors]) # this is the actual reduction of the recursor

        #TODO : find what is the difference between params and indices

        #The number of parameters in the constructor is not necessarily
        #equal to the number of parameters in the recursor when we have
        #nested inductive types. 
        nparams = len(major_args) - rule.num_fields
        # apply fields from major premise
        selected_major_args = major_args[nparams: nparams + rule.num_fields]
        if len(selected_major_args) != rule.num_fields: raise RecursorError("Major premise does not have the expected number of fields.")
        rhs = fold_apps(rhs, selected_major_args) # reapply the indices' arguments back

        # the remaining arguments are not relevant for the recursor; they are just applied back to whatever we got from the reduction
        if len(rec_args) > major_index + 1: rhs = fold_apps(rhs, rec_args[major_index + 1:])
        
        return rhs
    
    @typechecked
    #@profile
    def whnf_fvar(self, fvar : FVar, cheap_rec : bool, cheap_proj : bool) -> Expression:
        fvar_val = self.get_value_of_fvar(fvar) 
        if fvar_val is None:
            return fvar
        else:
            return self.whnf_core(fvar_val, cheap_rec=cheap_rec, cheap_proj=cheap_proj) 

    @typechecked
    #@profile
    def whnf_core(self, expr : Expression, cheap_rec : bool, cheap_proj : bool) -> Expression:
        if isinstance(expr, BVar) or isinstance(expr, Sort) or isinstance(expr, Pi) or isinstance(expr, Lambda) or isinstance(expr, NatLit) or isinstance(expr, StringLit) or isinstance(expr, Const): return expr
        elif isinstance(expr, FVar):
            if not expr.is_let: return expr # the fvar has no val that can be reduced to
        
        cached_whnfed_expr = self.whnf_core_cache.get(expr)
        if cached_whnfed_expr is not None: return cached_whnfed_expr

        r = None
        if isinstance(expr, FVar):
            return self.whnf_fvar(expr, cheap_rec=cheap_rec, cheap_proj=cheap_proj)
        elif isinstance(expr, Proj):
            pos_red = self.reduce_proj(expr, cheap_rec=cheap_rec, cheap_proj=cheap_proj) 
            if pos_red is None:
                r = expr
            else:
                r = self.whnf_core(pos_red, cheap_rec=cheap_rec, cheap_proj=cheap_proj)     
        elif isinstance(expr, App):
            raw_fn, raw_args = unfold_app(expr)
            
            fn = self.whnf_core(raw_fn, cheap_rec=cheap_rec, cheap_proj=cheap_proj)
            if isinstance(fn, Lambda):
                r = self.whnf_core(self.beta_reduction(fn, raw_args), cheap_rec=cheap_rec, cheap_proj=cheap_proj)
            elif fn is raw_fn:
                r = self.reduce_recursor(expr, cheap_rec=cheap_rec, cheap_proj=cheap_proj)
                if r is not None: 
                    red = self.whnf_core(r, cheap_rec=cheap_rec, cheap_proj=cheap_proj)
                    return red
                else: return expr
            else:
                r = self.whnf_core(fold_apps(fn, raw_args), cheap_rec=cheap_rec, cheap_proj=cheap_proj)
        elif isinstance(expr, Let):
            r = self.whnf_core(instantiate_bvar(body=expr.body, val=expr.val), cheap_rec=cheap_rec, cheap_proj=cheap_proj)
        
        if r is None:
            raise PanicError(f"Expr of type {expr.__class__.__name__} could not be matched, this should not happen.")

        if not cheap_proj: self.whnf_core_cache.put(expr, r)

        return r
    
    @typechecked
    #@profile
    def whnf(self, init_expr : Expression) -> Expression:
        """
        More powerful version of whnf_core that aggressively unfolds definitions.
        """
        if isinstance(init_expr, BVar) or isinstance(init_expr, Sort) or isinstance(init_expr, Pi) or isinstance(init_expr, Lambda) or isinstance(init_expr, NatLit) or isinstance(init_expr, StringLit): return init_expr # easy, non-reducible cases

        # we don't check cache results for trivial cases
        cached_whnfed_expr = self.whnf_cache.get(init_expr)
        if cached_whnfed_expr is not None: return cached_whnfed_expr

        # harder cases
        expr = init_expr
        while True:
            expr = self.whnf_core(expr, cheap_rec=False, cheap_proj=False)

            v = self.reduce_native(expr)
            if v is not None:
                self.whnf_cache.put(init_expr, v)
                return v

            r_expr = self.reduce_nat_lit(expr)
            if r_expr is not None: 
                # cache the result of nat_lit reduction
                self.whnf_cache.put(expr, r_expr)
                return r_expr
            
            unfolded = self.delta_reduction(expr)
            if unfolded is None:
                # cache the result if it was NOT delta reduced
                self.whnf_cache.put(init_expr, expr)
                return expr
            expr = unfolded

    # TYPE INFERENCE
    @typechecked
    #@profile
    def infer_fvar(self, fvar : FVar):
        return self.get_type_of_fvar(fvar)
    
    @typechecked
    #@profile
    def infer_app(self, app : App, infer_only : bool) -> Expression:
        if infer_only:
            # If infer_only is true we only check that the type of fn is a pi type and keep substituting the arguments into the function type's body_type. We don't check that arguments match the function type's domain.
            fn, args = unfold_app(app)
            fn_type = self.infer_core(fn, infer_only=(self.allow_loose_infer and infer_only))
            for arg in args:
                fn_type = self.ensure_pi(fn_type)
                
                fn_type = self.instantiate(
                    body=fn_type.body_type, 
                    val=arg
                )
            return fn_type
        else:
            # the function should be a pi type
            fn_type = self.ensure_pi(self.infer_core(app.fn, infer_only=(self.allow_loose_infer and infer_only)))
            
            # get the type of the argument
            inferred_arg_type = self.infer_core(app.arg, infer_only=(self.allow_loose_infer and infer_only))

            # the domain of the function should be equal to the type of the argument
            if not self.def_eq(fn_type.arg_type, inferred_arg_type):
                raise ExpectedDifferentTypesError(fn_type.arg_type, inferred_arg_type)
            
            infered_type = self.instantiate(body=fn_type.body_type, val=app.arg)
            return infered_type
    
    @typechecked
    #@profile
    def infer_sort(self, sort : Sort) -> Expression:
        return Sort(LevelSucc(sort.level))

    @typechecked
    #@profile
    def infer_pi(self, pi : Pi, infer_only : bool) -> Expression:
        lhs = self.ensure_sort(self.infer_core(pi.arg_type, infer_only=(self.allow_loose_infer and infer_only)))

        fvar, inst_body_type = self.instantiate_fvar(
            bname=pi.bname, 
            arg_type=pi.arg_type, 
            arg_val=None,
            body=pi.body_type, 
        )
        rhs = self.ensure_sort(self.infer_core(inst_body_type, infer_only=(self.allow_loose_infer and infer_only)))
        if has_specific_fvar(rhs, fvar): # TODO : remove this after testing
            raise PanicError("FVar was not abstracted in the inferred type.")
        self.remove_fvar(fvar)

        return Sort(LevelIMax(lhs.level, rhs.level))
    
    @typechecked
    #@profile
    def ensure_sort(self, e : Expression) -> Sort:
        if isinstance(e, Sort): return e
        whnfd_e = self.whnf(e)
        if isinstance(whnfd_e, Sort): return whnfd_e
        
        raise ExpectedDifferentExpressionError(Sort, whnfd_e.__class__)
    
    @typechecked
    #@profile
    def infer_lambda(self, e : Lambda, infer_only : bool) -> Expression:
        if not infer_only:
            self.ensure_sort(self.infer_core(e.arg_type, infer_only=(self.allow_loose_infer and infer_only))) # have to clone the arg_type since we are using it
        bname = e.bname
        fvar, inst_body = self.instantiate_fvar(
            bname=bname, 
            arg_type=e.arg_type, 
            arg_val=None,
            body=e.body 
        )
        infered_body_type = self.infer_core(inst_body, infer_only=(self.allow_loose_infer and infer_only))
        infered_pi = Pi(bname, e.arg_type, self.abstract(fvar, infered_body_type))

        if has_specific_fvar(infered_pi, fvar): # TODO : remove this after testing
            raise PanicError("FVar was not abstracted in the inferred type.")

        return infered_pi
    
    @typechecked
    #@profile
    def infer_const(self, c : Const) -> Expression:
        # this always clones the type from the environment
        if len(c.lvl_params) != len(self.environment.get_declaration_under_name(c.name).info.lvl_params):
            raise PanicError("The number of level parameters of the constant does not match the number of level parameters in the environment.")
        return self.environment.get_constant_type(c)
    
    @typechecked
    #@profile
    def make_let_binding(self, fvars : List[FVar], b : Expression) -> Expression:
        r = abstract_multiple_bvar(fvars, b)
        for i in range(len(fvars)-1, -1, -1):
            c_fvar = fvars[i]
            assert c_fvar.is_let
            assert c_fvar.val is not None

            abs_type = abstract_multiple_bvar(fvars[:i][::-1], c_fvar.type) # TODO : optimization here
            abs_val = abstract_multiple_bvar(fvars[:i][::-1], c_fvar.val)
            r = Let(bname=c_fvar.name, arg_type=abs_type, val=abs_val, body=r)
            assert not has_specific_fvar(r, c_fvar), "The fvar was not abstracted in the inferred type."
        return r

    @typechecked
    #@profile
    def infer_let(self, e : Let, infer_only : bool) -> Expression:
        if not infer_only:
            self.ensure_sort(self.infer_core(e.arg_type, infer_only=(self.allow_loose_infer and infer_only)))
            inferred_val_type = self.infer_core(e.val, infer_only=(self.allow_loose_infer and infer_only))
            if not self.def_eq(inferred_val_type, e.arg_type):
                raise ExpectedDifferentTypesError(inferred_val_type, e.arg_type)

        fvar, inst_body = self.instantiate_fvar( # for let expression we use fvars; it is up to the wnhf to further unfold the var later
            bname=e.bname,
            arg_type=e.arg_type,
            arg_val=e.val, 
            body=e.body, 
            is_let=True
        )
        inferred_type = self.infer_core(inst_body, infer_only=(self.allow_loose_infer and infer_only))

        if has_specific_fvar(inferred_type, fvar): # TODO : remove this after testing
            assert not has_specific_fvar(fvar.type, fvar), "The type of the fvar should not contain the fvar."
            assert fvar.type is e.arg_type, "This should be unreachable."
            assert fvar.val is e.val, "This should be unreachable."

            inferred_type_abstracted = self.abstract(fvar, inferred_type)
            return Let(e.bname, e.arg_type, e.val, inferred_type_abstracted)
        
        self.remove_fvar(fvar)
        return inferred_type
    
    @typechecked
    #@profile
    def proj_get_constructor(self, proj : Proj, infer_only : bool) -> Optional[Tuple[Const, InductiveType, Constructor, List[Expression]]]:
        """Returns the inductive type constant, the corresponding constructor, and the arguments to the constructor."""
        proj_name = proj.type_name
        struct_type = self.whnf(self.infer_core(proj.struct, infer_only=(self.allow_loose_infer and infer_only)))
        inductive_fn, args = unfold_app(struct_type)
        if not isinstance(inductive_fn, Const):
            return None
        if inductive_fn.name != proj_name: 
            return None
        
        inductive_decl = self.environment.get_inductive(inductive_fn.name)
        if inductive_decl.number_of_constructors() != 1: return None
        if len(args) != inductive_decl.num_params + inductive_decl.num_indices: return None
        
        constructor_decl = self.environment.get_constructor(inductive_decl.constructor_names[0]) # there is only one canonical constructor
        return inductive_fn, inductive_decl, constructor_decl, args

    @typechecked
    #@profile
    def infer_proj(self, proj : Proj, infer_only : bool) -> Expression:
        proj_index = proj.index

        pos_cons = self.proj_get_constructor(proj, infer_only=(self.allow_loose_infer and infer_only))
        if pos_cons is None: raise ProjectionError(f"Could not get constructor for projection {proj}")

        #I_name         I_info          c_info        (in the original code)
        inductive_name, inductive_decl, constructor, args = pos_cons 
        constructor_type = self.environment.get_declaration_type_with_substituted_level_params(constructor, inductive_name.lvl_params)
        assert inductive_decl.num_params == constructor.num_params, "Sanity check failed: number of parameters in inductive type and constructor do not match."
        
        for i in range(inductive_decl.num_params):
            constructor_type = self.whnf(constructor_type)
            if not isinstance(constructor_type, Pi):
                raise ProjectionError(f"Expected a Pi type when reducing parameters for constructor type but got {constructor_type.__class__}")
            if i >= len(args):
                raise ProjectionError(f"Ran out of arguments for parameters when reducing constructor type.")
            
            constructor_type = self.instantiate(body=constructor_type.body_type, val=args[i])

        #is_prop_type = self.is_prop(constructor_type) TODO: see next TODO
        for i in range(proj_index):
            constructor_type = self.whnf(constructor_type)
            if not isinstance(constructor_type, Pi):
                raise ProjectionError(f"Expected a Pi type when reducing indices for constructor type but got {constructor_type.__class__}")
            
            # TODO: the lean 4 code checks if the type has loose bvars (but how can this happen?). If is_prop_type it then ensures that the body remains a prop
            if has_loose_bvars(constructor_type):
                raise PanicError("Loose bvars in constructor type")

            constructor_type = self.instantiate(
                body=constructor_type.body_type,
                val=Proj(inductive_name.name, i, proj.struct), 
            )
        
        constructor_type = self.whnf(constructor_type)
        if not isinstance(constructor_type, Pi):
            raise ProjectionError(f"Expected a Pi type for projection index but got {constructor_type.__class__}")

        # TODO: the lean kernel does some checks regarding prop here
        return constructor_type.arg_type

    @typechecked
    #@profile
    def infer_nat_lit(self, n : NatLit) -> Expression:
        return Const(self.environment.Nat_name, [])
    
    @typechecked
    #@profile
    def infer_string_lit(self, s : StringLit) -> Expression:
        return Const(self.environment.String_name, [])

    @typechecked
    #@profile
    def infer_core(self, expr : Expression, infer_only : bool) -> Expression:
        """
        The main TC function: infers the type of an expression. If inference fails it raises an error. 
        Note that infer_core (infer_core expr) results in a Sort expression.

        Args:
            expr : Expression : The expression to infer the type of.
            infer_only : bool : If we know an expression is well-typed, we can use the `InferOnly` flag to skip some parts of the inference and checking.
        
        Returns:
            Expression : The inferred type of the expression.
        
        Raises: See KernelExceptions.py
        """
        has_fvar_not_in_context(expr, self.local_context) # TODO : remove this after testing

        # check if expression is already in infer_cache (separate cache for infer_only)
        cached_inferred_type = self.infer_cache[infer_only].get(expr)
        if cached_inferred_type is not None: return cached_inferred_type

        if isinstance(expr, BVar): raise PanicError("BVar should have been substituted when inferring")
        elif isinstance(expr, FVar): inferred_type = self.infer_fvar(expr) # we should not clone the fvar since we are using "is" to compare
        elif isinstance(expr, App): inferred_type = self.infer_app(expr, infer_only=(self.allow_loose_infer and infer_only))
        elif isinstance(expr, Sort): inferred_type = self.infer_sort(expr)
        elif isinstance(expr, Const): inferred_type = self.infer_const(expr) # const always copies the type of the const from the environment
        elif isinstance(expr, Lambda): inferred_type = self.infer_lambda(expr, infer_only=(self.allow_loose_infer and infer_only))
        elif isinstance(expr, Pi): inferred_type = self.infer_pi(expr, infer_only=(self.allow_loose_infer and infer_only))
        elif isinstance(expr, Let): inferred_type = self.infer_let(expr, infer_only=(self.allow_loose_infer and infer_only))
        elif isinstance(expr, Proj): inferred_type = self.infer_proj(expr, infer_only=(self.allow_loose_infer and infer_only))
        elif isinstance(expr, NatLit): inferred_type = self.infer_nat_lit(expr) # this always inferred_type=s a new const
        elif isinstance(expr, StringLit): inferred_type = self.infer_string_lit(expr) # this always inferred_type=s a new const
        else: raise ValueError(f"Unknown expression type {expr.__class__.__name__}")
        
        has_fvar_not_in_context(inferred_type, self.local_context) # TODO : remove this after testing

        # cache the result
        self.infer_cache[infer_only].put(expr, inferred_type)

        return inferred_type
    
    @typechecked
    #@profile
    def infer(self, expr : Expression) -> Expression:
        if not self.local_context.is_empty():
            raise PanicError(f"Local context is not empty when inferring: {self.local_context}")
        #rprint(f"CHECKING NEW EXPRESSION {expr}")
        inferred_type = self.infer_core(expr, infer_only=(self.allow_loose_infer and False))

        has_fvar_not_in_context(inferred_type, self.local_context) # TODO : remove this after testing
        return inferred_type

    # CHECKING DECLARATIONS
    @typechecked
    #@profile
    def check_declaration_info(self, info : DeclarationInfo):
        #print(f"CHECKING DECLARATION {info.name}")
        #print(f"INFO TYPE : {info.type}")
        if not are_unique_level_params(info.lvl_params):
            raise EnvironmentError(f"Level parameters in declaration info {info} are not unique.")
        if has_fvar(info.type):
            raise EnvironmentError(f"Type in declaration info {info} contains free variables.")

        inferred_type = self.infer(info.type)
        
        if not isinstance(inferred_type, Sort):
            raise EnvironmentError(f"Type of declaration info {info} is not a sort.")

    @typechecked
    #@profile
    def add_definition(self, name : Name, d : Definition):
        #rprint(f"ADDING DEFINITION : {name}")
        self.check_declaration_info(d.info)
        #rprint(f"VALUE : {d.value}")

        infered_type = self.infer(d.value)
        if not self.def_eq(infered_type, d.info.type):
            raise DeclarationError(f"Definition {name} has type {d.info.type} but inferred type {infered_type}")
        self.environment.add_declaration(name, d)

        #rprint(f"ADDED DEFINITION : {name}")
    
    @typechecked
    #@profile
    def add_theorem(self, name : Name, t : Theorem):
        #print(f"ADDING THEOREM : {name}")
        self.check_declaration_info(t.info)
        #print(t.value)

        infered_type = self.infer(t.value)
        if not self.def_eq(infered_type, t.info.type):
            raise DeclarationError(f"Theorem {name} has type {t.info.type} but inferred type {infered_type}")
        self.environment.add_declaration(name, t)

        #rprint(f"ADDED THEOREM : {name}")

    @typechecked
    #@profile
    def add_opaque(self, name : Name, o : Opaque):
        #rprint(f"ADDING OPAQUE : {name}")
        self.check_declaration_info(o.info)

        inferred_type = self.infer(o.value)
        if not self.def_eq(inferred_type, o.info.type):
            raise DeclarationError(f"Opaque {name} has type {o.info.type} but inferred type {inferred_type}")
        
        self.environment.add_declaration(name, o)

        #rprint(f"ADDED OPAQUE : {name}")

    @typechecked
    #@profile
    def add_axiom(self, name : Name, a : Axiom):
        #rprint(f"ADDING AXIOM : {name}")
        self.check_declaration_info(a.info)
        self.environment.add_declaration(name, a)

        #rprint(f"ADDED AXIOM : {name}")
    
    @typechecked
    #@profile
    def add_inductive(self, name : Name, ind : InductiveType):
        #rprint(f"ADDING INDUCTIVE : {name}")
        assert name == ind.info.name, "Sanity check failed: name does not match info name."
        
        self.environment.add_declaration(name, ind)

        self.check_inductive_declaration_infos(name)
        #rprint(f"ADDED INDUCTIVE : {name}")

    @typechecked
    #@profile
    def add_constructor(self, name : Name, constructor : Constructor):
        #rprint(f"ADDING CONSTRUCTOR: {name}")
        self.environment.add_declaration(name, constructor)
        self.check_inductive_declaration_infos(constructor.inductive_name)

        #rprint(f"ADDED CONSTRUCTOR : {name}")

    @typechecked
    #@profile
    def number_of_added_constructors(self, inductive_decl : InductiveType) -> int:
        count = 0
        for constructor_name in inductive_decl.constructor_names:
            if self.environment.exists_declaration_under_name(constructor_name):
                constructor_decl = self.environment.get_declaration_under_name(constructor_name)
                if not isinstance(constructor_decl, Constructor): raise DeclarationError(f"Inductive type's constructor name {inductive_decl.info.name} refers to a non-constructor {constructor_name}.")
                count += 1
        return count
    
    @typechecked
    #@profile
    def check_inductive_declaration_infos(self, inductive : Name): # CHANGES INDUCTIVE, BUT THIS IS OK
        """
        Inductive types are special in that they are defined cyclically: the constructors and the inductive type refer to each other cyclically. Thus we cannot check them as they are added to the environment. Instead, we check them once each part of the inductive definition has been added to the environment. We mark the inductive type and its constructors as checked once they have been successfully checked.
        """
        self.environment.checking_inductive = True # CHANGES INDUCTIVE, BUT THIS IS OK
        # First check that all the constructors have been added
        if not self.environment.exists_declaration_under_name(inductive): return
        inductive_decl = self.environment.get_declaration_under_name(inductive)
        if not isinstance(inductive_decl, InductiveType):
            raise DeclarationError(f"Inductive type {inductive} not found.")
        
        found_constructors = self.number_of_added_constructors(inductive_decl)
        if found_constructors < inductive_decl.number_of_constructors(): return
        assert(found_constructors == inductive_decl.number_of_constructors()), "Sanity check failed: number of found constructors does not match the number of expected constructors."

        self.check_declaration_info(inductive_decl.info)

        # Now check that the inductive type and its constructors are well-formed
        for i, constructor_name in enumerate(inductive_decl.constructor_names):
            constructor_decl = self.environment.get_declaration_under_name(constructor_name)
            self.check_declaration_info(constructor_decl.info)
            assert isinstance(constructor_decl, Constructor), f"Sanity check failed: constructor {constructor_name} is not a constructor."

            if i != constructor_decl.c_index:
                raise DeclarationError(f"Constructor {constructor_name} has index {constructor_decl.c_index} but should have index {i}.")

            if inductive_decl.num_params != constructor_decl.num_params:
                raise DeclarationError(f"Constructor {constructor_name} has {constructor_decl.num_params} parameters but the inductive type {constructor_decl.inductive_name} has {inductive_decl.num_params} parameters.")

        inductive_decl.is_checked = True
        for constructor_name in inductive_decl.constructor_names:
            constructor_decl = self.environment.get_declaration_under_name(constructor_name)
            assert isinstance(constructor_decl, Constructor), f"Sanity check failed: constructor {constructor_name} is not a constructor."
            constructor_decl.is_checked = True # CHANGES INDUCTIVE, BUT THIS IS OK
        self.environment.checking_inductive = False # CHANGES INDUCTIVE, BUT THIS IS OK

    @typechecked
    #@profile
    def add_recursor(self, name : Name, recursor : Recursor):
        #rprint(f"ADDING RECURSOR : {name}")
        self.check_declaration_info(recursor.info)
        self.environment.add_declaration(name, recursor) # add the recursor to the environment before checking the recursion rules, since they refer to the recursor

        for rec_rule in recursor.recursion_rules:
            constructor_decl = self.environment.get_declaration_under_name(rec_rule.constructor)
            if not isinstance(constructor_decl, Constructor):
                raise DeclarationError(f"Recursor rule {rec_rule} is not associated with a constructor; found {constructor_decl.__class__.__name__} with name {constructor_decl.info.name} instead.")
            
            # TODO: why is there a problem here with Lean.IR....?
            #if constructor_decl.num_params != recursor.num_params:
            #    raise DeclarationError(f"Recursor rule {rec_rule} is associated with constructor {constructor_decl.info.name} which has {constructor_decl.num_params} parameters, but the recursor {recursor.info.name} has {recursor.num_params} parameters.")

        #rprint(f"ADDED RECURSOR : {name}")

    @typechecked
    #@profile
    def add_quotient(self, name : Name, q : Quot):
        #rprint(f"ADDING QUOTIENT : {name}")
        self.check_declaration_info(q.info)
        self.environment.add_declaration(name, q)

        #rprint(f"ADDED QUOTIENT : {name}")

    @typechecked
    #@profile
    def add_declaration(self, name : Name, decl : Declaration):
        if isinstance(decl, Definition): self.add_definition(name, decl)
        elif isinstance(decl, Theorem): self.add_theorem(name, decl)
        elif isinstance(decl, Opaque): self.add_opaque(name, decl)
        elif isinstance(decl, Axiom): self.add_axiom(name, decl)
        elif isinstance(decl, InductiveType): self.add_inductive(name, decl)
        elif isinstance(decl, Constructor): self.add_constructor(name, decl)
        elif isinstance(decl, Recursor): self.add_recursor(name, decl)
        elif isinstance(decl, Quot): self.add_quotient(name, decl)
        else: raise ValueError(f"Unknown declaration type {decl.__class__.__name__}")