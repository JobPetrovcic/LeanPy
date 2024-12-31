from typing import List, Optional, Tuple

from typeguard import typechecked
from Structures.Environment.Declaration import Axiom, Constructor, Declaration, DeclarationInfo, Definition, InductiveType, Opaque, Quot, Recursor, Theorem, compare_reducibility_hints
from Structures.Environment.DeclarationManipulation import is_structural_inductive
from Structures.Environment.Environment import Environment
from Structures.Environment.LocalContext import LocalContext
from Structures.Environment.NatReduction import *
from Structures.Expression.Expression import *
from Structures.Expression.ExpressionManipulation import ReductionStatus, abstract_bvar, clone_expression, do_fn, fold_apps, has_loose_bvars, has_specific_fvar, instantiate_bvar, has_fvars, level_zip, substitute_level_params_in_expression, unfold_app, get_app_function
from Structures.Expression.Level import *
from Structures.Expression.LevelManipulation import antisymm_eq, antisymm_eq_list, are_unique_level_params, clone_level, is_zero_level
from Structures.KernelErrors import ExpectedDifferentExpressionError, ExpectedDifferentTypesError, PanicError, ProjectionError, EnvironmentError, DeclarationError
from Structures.Name import Name
import warnings

import sys
sys.setrecursionlimit(10**6) 

#TODO s:
# - special cases for Nat and String literals
# - quot
# - use reducibility hints
# - proof irrelevant inequality
# - understand K-axiom
# - understand lazy delta reduction and make sure it is implemented correctly

def dprint(s : str):
    print(s)

r_print : bool = True
def rprint(s : str):
    if r_print:
        print(s)

def has_fvar_not_in_context(body : Expression, context : LocalContext):
    """ Raises an error if the given expression contains a free variable not in the given context. """
    def fn(expr : Expression):
        if isinstance(expr, FVar) and expr not in context.fvars: raise ValueError(f"In body\n\t{body}\n\n found free variable\n\t{expr}\n\n not in context {context}")
    do_fn(body, fn)

class TypeChecker:
    def __init__(self):
        self.environment = Environment()
        self.local_context = LocalContext()

    # LOCAL CONTEXT INTERACTIONS
    @profile
    @typechecked
    def remove_fvar(self, fvar: FVar):
        self.local_context.remove_fvar(fvar)
    
    @profile
    @typechecked
    def get_type_of_fvar(self, fvar : FVar) -> Expression:
        return self.local_context.get_fvar_type(fvar, use_same_fvars=True)
    
    @profile
    @typechecked
    def get_value_of_fvar(self, fvar : FVar) -> Optional[Expression]:
        return self.local_context.get_fvar_value(fvar, use_same_fvars=True)
    
    @profile
    @typechecked
    def instantiate(self, body : Expression, val : Expression, clone_body : bool, clone_val : bool, use_same_fvars : bool = True) -> Expression:
        """
        Replace the outermost bound variable in the body with the value. Clones the body if needed.
        If clone_val is true, then the value is cloned EVERY TIME it is used.
        """
        return instantiate_bvar(body, val, clone_body=clone_body, clone_val=clone_val, use_same_fvars=use_same_fvars)
    
    @profile
    @typechecked
    def create_fvar(self, name: Name, type: Expression, val : Optional[Expression], is_let : bool) -> FVar:
        fvar = FVar(name, type, val, is_let=is_let)
        self.local_context.add_fvar(fvar)
        return fvar

    @profile
    @typechecked
    def instantiate_fvar(
            self, 
            bname : Name, 
            arg_type : Expression, # the type of the fvar
            arg_val : Optional[Expression],  # the value of the fvar
            body : Expression, # the body in which the fvar is instantiated
            clone : bool, 
            is_let : bool = False
        ) -> Tuple[FVar, Expression]:
        fvar = self.create_fvar(bname, arg_type, arg_val, is_let=is_let)
        return fvar, self.instantiate(body, fvar, clone_body=clone, clone_val=False)
    
    @profile
    @typechecked
    def instantiate_fvar_multiple_bodies(
            self, 
            bname : Name, 
            arg_type : Expression, # the type of the fvar
            arg_val : Optional[Expression], # the value of the fvar
            bodies : List[Expression], # the bodies in which the fvar is instantiated
            clone : bool, 
            is_let : bool = False) -> Tuple[FVar, List[Expression]]:
        fvar = self.create_fvar(bname, arg_type, arg_val, is_let=is_let)
        return fvar, [self.instantiate(body, fvar, clone_body=clone, clone_val=False) for body in bodies]
    
    def abstract(self, fvar : FVar, expr : Expression, clone : bool, use_same_fvars : bool) -> Expression:
        """Abstracts the outermost bound variable in the given expression."""
        # remove the fvar from the local context
        self.remove_fvar(fvar)
        abstract_expression = abstract_bvar(expr, fvar, clone=clone, use_same_fvars=use_same_fvars)
        if has_specific_fvar(abstract_expression, fvar): # TODO : remove this after testing
            raise PanicError("FVar was not abstracted in the inferred type.")
        return abstract_expression
    
    # HELPERS
    @profile
    @typechecked
    def is_structure_like(self, decl_name : Name) -> bool:
        decl = self.environment.get_declaration_under_name(decl_name)
        if not isinstance(decl, InductiveType): return False
        return is_structural_inductive(decl) and decl.num_indices == 0 and not decl.is_recursive
    
    @profile
    @typechecked
    def is_prop(self, e : Expression, clone : bool):
        inferred_type = self.whnf(self.infer_core(e, clone=clone, infer_only=True), clone=False, unfold_definition=True)
        return isinstance(inferred_type, Sort) and is_zero_level(inferred_type.level)
    
    # NATIVE REDUCTIONS: natural number and string literals are converted to applications of constructors
    @profile
    @typechecked
    def nat_lit_to_constructor(self, nat_lit : NatLit) -> Expression:
        """ Returns the constructor form of the given natural literal. """
        if nat_lit.val == 0: return Const(name=self.environment.Nat_zero_name, lvl_params=[])
        return App(
            Const(name=self.environment.Nat_succ_name, lvl_params=[]),
            NatLit(nat_lit.val-1)
        )
    
    @profile
    @typechecked
    def char_to_expression(self, c : str) -> Expression:
        return App(
            Const(name=self.environment.Char_name, lvl_params=[]),
            NatLit(ord(c))
        )

    @profile
    @typechecked
    def str_to_char_list(self, s : str, ind : int = 0) -> Expression:
        assert ind >= 0, "Index must be non-negative when converting a string literal to a constructor."
        if ind == len(s): 
            return App(
                Const(name=self.environment.List_nil_name, lvl_params=[self.environment.level_one]),
                Const(name=self.environment.Char_name, lvl_params=[])
            )
        else:
            return  App(
                App(
                    App(
                        Const(name=self.environment.List_cons_name, lvl_params=[self.environment.level_one]),
                        Const(name=self.environment.Char_name, lvl_params=[])
                    ),
                    self.char_to_expression(s[ind])
                ),
                self.str_to_char_list(s, ind+1)
            )

    @profile
    @typechecked
    def str_lit_to_constructor(self, s : StringLit) -> Expression:
        char_list = self.str_to_char_list(s.val, 0)
        return App(
            Const(name=self.environment.String_mk_name, lvl_params=[]),
            char_list
        )

    # DEFINITIONAL EQUALITY
    @profile
    @typechecked
    def def_eq_sort(self, l : Sort, r : Sort) -> bool:
        """Sorts are equal if their levels satisfy antisymmetry.
        The comparsion function does not change anything, so def_eq_sort is safe to use when passing by reference.
        """
        return antisymm_eq(l.level, r.level)

    @profile
    @typechecked
    def def_eq_const(self, l : Const, r : Const) -> bool:
        """
        If the names are the same, and the level parameters are equal, then the constants are equal.
        Since nothing is changed, this function is safe to use when passing by reference.
        """
        return l.name == r.name and antisymm_eq_list(l.lvl_params, r.lvl_params)

    @profile
    @typechecked
    def def_eq_bvar(self, l : BVar, r : BVar) -> bool:
        raise PanicError("BVar should have been substituted by now, when comparing expressions for definitional equality.")

    @profile
    @typechecked
    def def_eq_fvar(self, l : FVar, r : FVar) -> bool:
        """
        For FVars, we are using the "is" operator to compare them. 
        They are only a place holder for the actual type, so this is enough. However, care must be taken when cloning.
        """
        return l is r

    @profile
    @typechecked
    def def_eq_app(self, l : App, r : App, clone : bool) -> bool:
        f_fn, f_args = unfold_app(l.fn)
        g_fn, g_args = unfold_app(r.fn)
        if not self.def_eq_core(f_fn, g_fn, clone=clone):
            return False
        
        if len(f_args) != len(g_args): return False
        for f_arg, g_arg in zip(f_args, g_args):
            if not self.def_eq_core(f_arg, g_arg, clone=clone):
                return False
        return True

    @profile
    @typechecked
    def def_eq_pi(self, l: Pi, r: Pi, clone : bool) -> bool:
        if not self.def_eq_core(l.arg_type, r.arg_type, clone=True): # we have to clone the argument type since it is used later
            return False
        
        fvar, (l_n, r_n) = self.instantiate_fvar_multiple_bodies(
            bname=l.bname, 
            arg_type=l.arg_type, 
            arg_val=None, 
            bodies=[l.body_type, r.body_type], 
            clone=clone, 
        )
        
        result = self.def_eq_core(l_n, r_n, clone=False) # n_l and n_r are (possibly) already separated from l and r when instantiated, so def_eq can do whatever it wants
        self.remove_fvar(fvar)
        return result

    @profile
    @typechecked
    def def_eq_lambda(self, l : Lambda, r : Lambda, clone : bool) -> bool: # CLONE CHECKED
        if not self.def_eq_core(l.arg_type, r.arg_type, clone=True): # we have to clone the argument type since it is used later
            return False
        
        fvar, (l_n, r_n) = self.instantiate_fvar_multiple_bodies(
            bname=l.bname, 
            arg_type=l.arg_type, 
            arg_val=None,
            bodies=[l.body, r.body], 
            clone=clone
        )
        ret = self.def_eq_core(l_n, r_n, clone=False) # n_l and n_r are already separated from l and r when instantiated, so def_eq can do whatever it wants
        self.remove_fvar(fvar)
        return ret
    
    @profile
    @typechecked
    def def_eq_proj(self, l : Proj, r : Proj, clone : bool) -> Optional[bool]: # CLONE CHECKED
        if l.index != r.index: return None
        if self.lazy_delta_proj_reduction(l, r, l.index, clone=clone):
            return True
        return None

    @profile
    @typechecked
    def try_structural_eta_expansion_core(self, t : Expression, s : Expression, clone : bool) -> bool: # CLONE CHECKED
        # First part: deconstruct s, ensure it is an application of a constructor
        s_fn, s_args = unfold_app(s)

        if not isinstance(s_fn, Const): return False
        
        decl = self.environment.get_declaration_under_name(s_fn.name)
        if not isinstance(decl, Constructor): return False

        # Second part: ensure that the application has the correct number of arguments and that the induective type is a structure
        if len(s_args) != decl.num_params + decl.num_fields: return False
        if not self.is_structure_like(decl.inductive_name): return False

        # Third part: ensure that the types are equal
        if not self.def_eq_core(
            self.infer_core(t, clone=True, infer_only=True), # clone since we use t later
            self.infer_core(s, clone=True, infer_only=True), # clone since we use s later
            clone=False
        ): return False

        # Fourth part: ensure that the arguments are equal:
        # s was decomposed, so we know the arguments
        # for t we don't know the arguments, so we use proj to get them
        for i in range(decl.num_params, len(s_args)):
            # TODO: what name should be used here?
            #dprint(f"2create proj with type_name {decl.inductive_name}")
            t_i_proj = Proj(type_name=decl.inductive_name, index=i-decl.num_params, struct=clone_expression(t, use_same_fvars=True))
            use_s_arg_i = clone_expression(s_args[i], use_same_fvars=True) if clone else s_args[i]

            # compare the arguments
            if not self.def_eq_core(t_i_proj, use_s_arg_i, clone=False): return False
        return True

    def try_structural_eta_expansion(self, l : Expression, r : Expression, clone : bool) -> bool:
        # TODO: use wrappers here
        # clone the first time to not mess up the expression for the second time, the second time clone iff clone is true
        return self.try_structural_eta_expansion_core(l, r, True) or self.try_structural_eta_expansion_core(r, l, clone)
    
    def try_eta_expansion_core(self, t : Expression, s : Expression, clone : bool) -> bool:
        # TODO: use wrappers here
        """
        Tries to eta expand s: if s is a function, then by eta expansion, it is equal to the expression "fun x => s x".
        Always assumes that t and s were cloned beforehand.
        """
        if not ((isinstance(t, Lambda) and not isinstance(s, Lambda))): return False
        s_type = self.whnf(self.infer_core(s, clone=True, infer_only=True), clone=False, unfold_definition=False)
        if not isinstance(s_type, Pi): return False
        new_s = Lambda(bname=s_type.bname, arg_type=s_type.arg_type, body=App(s, BVar(0)))
        use_t = clone_expression(t, use_same_fvars=True) if clone else t
        return self.def_eq_core(use_t, new_s, clone=False)

    def try_eta_expansion(self, t : Expression, s : Expression, clone : bool) -> bool:
        # TODO: use wrappers here
        """
        Tries to eta expand y and compares it to x, then tries to eta expand x and compares it to y.
        Always assumes that x and y were cloned beforehand.
        """
        if (isinstance(t, Lambda) and not isinstance(s, Lambda)): return self.try_eta_expansion_core(t, s, clone)
        elif (isinstance(s, Lambda) and not isinstance(t, Lambda)): return self.try_eta_expansion_core(s, t, clone)
        return False
    
    def def_eq_easy(self, l: Expression, r: Expression) -> Optional[bool]:
        if isinstance(l, Sort) and isinstance(r, Sort):
            return self.def_eq_sort(l, r)
        elif isinstance(l, BVar) and isinstance(r, BVar):
            return self.def_eq_bvar(l, r)
        elif isinstance(l, FVar) and isinstance(r, FVar):
            return self.def_eq_fvar(l, r)
        
    def is_def_eq_proof_irrel(self, t : Expression, s : Expression, clone : bool) -> Optional[bool]:
        # TODO : integrate this into def_eq_core
        # Proof irrelevance support for Prop (aka Type.{0})
        t_type = self.infer_core(t, clone=clone, infer_only=True)
        if not self.is_prop(t_type, clone=False): # since type is (potentially) already cloned
            return None
        s_type = self.infer_core(s, clone=clone, infer_only=True)
        return self.def_eq_core(t_type, s_type, clone=clone)

    def def_eq_core(self, l: Expression, r: Expression, clone : bool) -> bool:
        if l is r: return True
        
        #lid = id(l)
        #rid = id(r)
        #dprint(f"l {lid}: {l} {l.__class__}")
        #dprint(f"r {rid}: {r} {r.__class__}")

        is_easy = self.def_eq_easy(l, r) # no cloning needed
        if is_easy is not None: return is_easy

        if isinstance(l, Const) and isinstance(r, Const):
            if self.def_eq_const(l, r): return True

        l_n = self.whnf(l, clone=clone, unfold_definition=False)
        r_n = self.whnf(r, clone=clone, unfold_definition=False)
        #dprint(f"l_n: {l_n}")
        #dprint(f"r_n: {r_n}")

        if (l_n is not l) or (r_n is not r):
            is_easy = self.def_eq_easy(l_n, r_n)
            if is_easy is not None: return is_easy

        is_proof_irr = self.is_def_eq_proof_irrel(l_n, r_n, clone=True)
        if is_proof_irr is not None: return is_proof_irr

        l_n_n, r_n_n, try_lazy = self.lazy_delta_reduction(l_n, r_n, clone=clone)
        if try_lazy is not None: return try_lazy

        if isinstance(l_n_n, Const) and isinstance(r_n_n, Const):
            if self.def_eq_const(l_n_n, r_n_n): return True

        if (l_n_n is not l) or (r_n_n is not r):
            is_easy = self.def_eq_easy(l_n_n, r_n_n)
            if is_easy is not None: return is_easy
        
        if isinstance(l_n_n, App) and isinstance(r_n_n, App):
            if self.def_eq_app(l_n_n, r_n_n, clone=True): return True
        if isinstance(l_n_n, Pi) and isinstance(r_n_n, Pi):
            if self.def_eq_pi(l_n_n, r_n_n, clone=True): return True
        if isinstance(l_n_n, Lambda) and isinstance(r_n_n, Lambda):
            if self.def_eq_lambda(l_n_n, r_n_n, clone=True): return True
        if isinstance(l_n_n, Proj) and isinstance(r_n_n, Proj):
            if self.def_eq_proj(l_n_n, r_n_n, clone=True): return True

        # finally try unfolding everything
        l_n_n_n = self.whnf(l_n_n, clone=False, unfold_definition=True)
        r_n_n_n = self.whnf(r_n_n, clone=False, unfold_definition=True)

        # Reductions
        if self.try_structural_eta_expansion(l_n_n_n, r_n_n_n, True):
            return True
        if self.try_eta_expansion(l_n_n_n, r_n_n_n, False): # l_n_n_n and r_n_n_n are already whnfed and so cloned, therefore, try_eta_expansion can do whatever it wants
            return True

        return False
    
    # REDUCTIONS
    def beta_reduction(self, expr : App, clone : bool) -> Expression: # CLONE CHECKED
        """
        Reduces the application by substituting the argument in the body.
        """
        f, args = unfold_app(expr)
        n_successful_subs = 0
        f = clone_expression(f, use_same_fvars=True) if clone else f
        for arg in args:
            if isinstance(f, Lambda):
                f = self.instantiate(
                    body=f.body, 
                    val=arg, 
                    clone_body=False,
                    clone_val=True,
                )
                n_successful_subs += 1
            else:
                break

        return fold_apps(f, args[n_successful_subs:])

    def zeta_reduction(self, expr : Let, clone : bool) -> Expression: # CLONE CHECKED
        """
        Reduces the let expression by substituting the fvar with the value of the let expression into the body.
        """
        _, sub_expr = self.instantiate_fvar( # for let expression we use fvars; it is up to the wnhf to further unfold the fvar later
            bname=expr.bname,
            arg_type=expr.arg_type,
            arg_val=expr.val, 
            body=expr.body, 
            clone=clone, 
            is_let=True
        )
        return sub_expr

    @profile
    @typechecked
    def delta_const(self, c : Const) -> Optional[Expression]: # CLONE CHECKED
        """Returns the value of the constant if it can be unfolded, otherwise return None."""
        decl = self.environment.get_declaration_under_name(c.name)
        if not decl.has_value():
            return None
        
        assert isinstance(decl, Definition) or isinstance(decl, Opaque) or isinstance(decl, Theorem)
        return self.environment.get_cloned_val_with_substituted_level_params(decl, c.lvl_params)
    
    @profile
    @typechecked
    def is_delta(self, expr : Expression) -> Optional[Tuple[Const, Definition | Opaque | Theorem, List[Expression]]]: # CLONE CHECKED
        fn, args = unfold_app(expr)
        if not isinstance(fn, Const): return None
        if not self.environment.exists_declaration_under_name(fn.name): return None
        decl = self.environment.get_declaration_under_name(fn.name)
        if not decl.has_value(): return None
        assert isinstance(decl, Definition) or isinstance(decl, Opaque) or isinstance(decl, Theorem)
        return fn, decl, args

    def delta_reduction_core(self, fn : Const, decl : Definition | Opaque | Theorem, args : List[Expression]) -> Expression:
        assert fn.name == decl.info.name
        decl_val = self.environment.get_cloned_val_with_substituted_level_params(decl, fn.lvl_params)
        return fold_apps(decl_val, args)

    @profile
    @typechecked
    def delta_reduction(self, expr : Expression, clone : bool) -> Optional[Expression]: # CLONE CHECKED
        """ Unfolds the applications of the expression. If the function is a declaration, then it unfolds it. """
        expr = clone_expression(expr, use_same_fvars=True) if clone else expr

        is_d = self.is_delta(expr)
        if is_d is None: return None
        return self.delta_reduction_core(*is_d)
    
    @profile
    @typechecked
    def reduce_proj_core(self, proj_struct : Expression, idx : int) -> Optional[Expression]: # CLONE CHECKED, CHECKED
        """ If we have a projection of an expression that is an application of a constructor, then we reduce it to the corresponding argument of the constructor. 
        
        For example, proj 0 (Prod.mk (A) (B) (a : A) (b : B)) would be reduced to a. Note that in this case A B are parameters of the constructor, and a and b are the actual arguments, used in the projection.
        """
        if isinstance(proj_struct, StringLit):
            proj_struct = self.str_lit_to_constructor(proj_struct)
        
        proj_struct_fn, proj_struct_args = unfold_app(proj_struct)
        if not isinstance(proj_struct_fn, Const): return None
        constructor_decl = self.environment.get_declaration_under_name(proj_struct_fn.name)
        if not isinstance(constructor_decl, Constructor): return None

        if constructor_decl.num_params + idx >= len(proj_struct_args): return None

        return proj_struct_args[constructor_decl.num_params + idx]
    
    def reduce_proj(self, proj : Proj, clone : bool, cheap_proj : bool) -> Optional[Expression]: # CLONE CHECKED
        idx = proj.index
        c = clone_expression(proj.struct, use_same_fvars=True) if clone else proj.struct
        c = self.whnf_core(c, clone=False, cheap_proj=cheap_proj) if cheap_proj else self.whnf(c, clone=False, unfold_definition=True)
        return self.reduce_proj_core(c, idx)
    
    #@profile
    @profile
    @typechecked
    def lazy_delta_reduction_step(self, t_n : Expression, s_n : Expression) -> Tuple[Expression, Expression, ReductionStatus]:
        id_t = self.is_delta(t_n)
        id_s = self.is_delta(s_n)

        if (id_t is None) and (id_s is None): return t_n, s_n, ReductionStatus.UNKNOWN
        elif (id_t is not None) and (id_s is None):
            t_n_n = self.whnf_core(self.delta_reduction_core(*id_t), clone=False, cheap_proj=False)
            s_n_n = s_n
        elif (id_t is None) and (id_s is not None):
            s_n_n = self.whnf_core(self.delta_reduction_core(*id_s), clone=False, cheap_proj=False)
            t_n_n = t_n
        elif (id_t is not None) and (id_s is not None):
            hint_compare = compare_reducibility_hints(id_t[1], id_s[1])
            if hint_compare < 0: 
                t_n_n = self.whnf_core(self.delta_reduction_core(*id_t), clone=False, cheap_proj=False)  # reduce t
                s_n_n = s_n
            elif hint_compare > 0: 
                t_n_n = t_n
                s_n_n = self.whnf_core(self.delta_reduction_core(*id_s), clone=False, cheap_proj=False)
            else: # reduce both
                t_n_n = self.whnf_core(self.delta_reduction_core(*id_t), clone=False, cheap_proj=False)
                s_n_n = self.whnf_core(self.delta_reduction_core(*id_s), clone=False, cheap_proj=False)
        else:
            raise PanicError("Unreachable code reached in lazy_delta_reduction_step.")

        is_easy = self.def_eq_easy(t_n_n, s_n_n)
        if is_easy is not None:
            return t_n_n, s_n_n, (ReductionStatus.EQUAL if is_easy else ReductionStatus.NOT_EQUAL)
        else: return t_n_n, s_n_n, ReductionStatus.CONTINUE
    
    #@profile
    @profile
    @typechecked
    def lazy_delta_reduction(self, t_n : Expression, s_n : Expression, clone : bool) -> Tuple[Expression, Expression, Optional[bool]]:
        t_n = clone_expression(t_n, use_same_fvars=True) if clone else t_n
        s_n = clone_expression(s_n, use_same_fvars=True) if clone else s_n
        while True:
            if isinstance(t_n, NatLit) or isinstance(s_n, NatLit): raise NotImplementedError("Nat literals are not implemented yet.")

            t_n, s_n, status = self.lazy_delta_reduction_step(t_n, s_n)
            if status == ReductionStatus.CONTINUE: pass
            elif status == ReductionStatus.EQUAL: return t_n, s_n, True
            elif status == ReductionStatus.NOT_EQUAL: return t_n, s_n, False
            elif status == ReductionStatus.UNKNOWN: return t_n, s_n, None
            else: raise PanicError("Unknown reduction status.")

    def lazy_delta_proj_reduction(self, t_n : Expression, s_n : Expression, idx : int, clone : bool) -> bool:
        t_n = clone_expression(t_n, use_same_fvars=True) if clone else t_n
        s_n = clone_expression(s_n, use_same_fvars=True) if clone else s_n
        while True:
            t_n, s_n, status = self.lazy_delta_reduction_step(t_n, s_n)
            if status is ReductionStatus.CONTINUE: pass
            elif status is ReductionStatus.EQUAL: return True
            else:
                t = self.reduce_proj_core(t_n, idx)
                if t is not None:
                    s = self.reduce_proj_core(s_n, idx)
                    if s is not None:
                        return self.def_eq_core(t, s, clone=False) # this is risky
                return self.def_eq_core(t_n, s_n, clone=False)

    def reduce_nat_lit(self, e : Expression, clone : bool) -> Optional[Expression]: # CLONE CHECKED
        if not isinstance(e, App): return None
        fn, args = unfold_app(e)
        if not isinstance(fn, Const): return None
        if len(args) == 1:
            if fn.name == self.environment.Nat_succ_name:
                arg = self.whnf(args[0], clone=clone, unfold_definition=True)
                if not isinstance(arg, NatLit): return None
                return NatLit(arg.val + 1)
        if len(args) == 2:
            arg1 = self.whnf(args[0], clone=clone, unfold_definition=True)
            if not isinstance(arg1, NatLit): return None
            arg2 = self.whnf(args[1], clone=clone, unfold_definition=True)
            if not isinstance(arg2, NatLit): return None
            
            name = fn.name
            if name == self.environment.Nat_add_name: return reduce_bin_nat_op(nat_add, arg1.val, arg2.val)
            elif name == self.environment.Nat_sub_name: return reduce_bin_nat_op(nat_sub, arg1.val, arg2.val)
            elif name == self.environment.Nat_mul_name: return reduce_bin_nat_op(nat_mul, arg1.val, arg2.val)
            elif name == self.environment.Nat_pow_name: return reduce_bin_nat_op(nat_pow, arg1.val, arg2.val)
            elif name == self.environment.Nat_gcd_name: return reduce_bin_nat_op(nat_gcd, arg1.val, arg2.val)
            elif name == self.environment.Nat_mod_name: return reduce_bin_nat_op(nat_mod, arg1.val, arg2.val)
            elif name == self.environment.Nat_div_name: return reduce_bin_nat_op(nat_div, arg1.val, arg2.val)
            elif name == self.environment.Nat_eq_name: return reduce_bin_nat_pred(nat_eq, arg1.val, arg2.val)
            elif name == self.environment.Nat_le_name: return reduce_bin_nat_pred(nat_le, arg1.val, arg2.val)
            elif name == self.environment.Nat_land_name: return reduce_bin_nat_op(nat_land, arg1.val, arg2.val)
            elif name == self.environment.Nat_lor_name: return reduce_bin_nat_op(nat_lor, arg1.val, arg2.val)
            elif name == self.environment.Nat_lxor_name: return reduce_bin_nat_op(nat_lxor, arg1.val, arg2.val)
            elif name == self.environment.Nat_shiftl_name: return reduce_bin_nat_op(nat_shiftl, arg1.val, arg2.val)
            elif name == self.environment.Nat_shiftr_name: return reduce_bin_nat_op(nat_shiftr, arg1.val, arg2.val)
            return n

    # INDUCTIVE
    #inductive stuff
    @profile
    @typechecked
    def get_first_constructor(self, inductive_name : Name) -> Optional[Constructor]: # CLONE CHECKED
        decl = self.environment.get_declaration_under_name(inductive_name)
        if not isinstance(decl, InductiveType): return None
        if decl.number_of_constructors() == 0: return None
        return self.environment.get_constructor(decl.constructor_names[0])
    
    # inductive stuff
    @profile
    @typechecked
    def expand_eta_struct(self, e_type : Expression, e : Expression):
        fn, args = unfold_app(e_type)
        if not isinstance(fn, Const): return e

        constructor = self.get_first_constructor(fn.name)
        if not constructor: return e

        assert len(args) >= constructor.num_params
        args = args[:constructor.num_params]
        result = fold_apps(Const(name=constructor.info.name, lvl_params=fn.lvl_params), args)
        #dprint(f"3create proj with type_name {fn.name}")
        result = fold_apps(result, [Proj(type_name=fn.name, index=i, struct=e) for i in range(constructor.num_fields)])
        return result
    
    # inductive stuff
    @profile
    @typechecked
    def to_constructor_when_structure(self, inductive_name : Name, e : Expression) -> Expression:
        if not self.is_structure_like(inductive_name): return e
        f = get_app_function(e)
        if isinstance(f, Const) and isinstance(self.environment.get_declaration_under_name(f.name), Constructor): return e

        e_type = self.whnf(self.infer_core(e, clone=True, infer_only=True), clone=False, unfold_definition=False)

        e_type_fn = get_app_function(e_type)
        if not (isinstance(e_type_fn, Const) and e_type_fn.name == inductive_name): return e 

        if self.is_prop(e_type, clone=True): return e
        return self.expand_eta_struct(e_type, e)
    
    # inductive stuff
    @profile
    @typechecked
    def mk_nullary_constructor(self, type_e : Expression, num_params : int) -> Optional[Expression]:
        d, args = unfold_app(type_e)
        if not isinstance(d, Const): return None
        constructor = self.get_first_constructor(d.name)
        if constructor is None: return None
        args = args[:num_params]
        return fold_apps(Const(name=constructor.info.name, lvl_params=d.lvl_params), args)

    # inductive stuff
    @profile
    @typechecked
    def to_constructor_when_K(self, recursor : Recursor, e : Expression) -> Expression:
        """See https://stackoverflow.com/questions/39239363/what-is-axiom-k
        For datatypes that support K-axiom, given `e` an element of that type, we convert (if possible)
        to the default constructor. For example, if `e : a = a`, then this method returns `eq.refl a` """
        assert recursor.isK, "Cannot apply K-axiom to a recursor that is not K."
        # TODO : understand this
        app_type = self.whnf(self.infer_core(e, clone=True, infer_only=True), clone=False, unfold_definition=True)
        app_type_inductive, _ = unfold_app(app_type)

        if not isinstance(app_type_inductive, Const): return e
        if app_type_inductive.name != recursor.get_major_induct(): return e # type incorrect

        new_constructor_app = self.mk_nullary_constructor(app_type, recursor.num_params)
        if not new_constructor_app: return e
        new_type = self.infer_core(new_constructor_app, clone=True, infer_only=True)

        if not self.def_eq_core(app_type, new_type, clone=False): # both cloned so no need to clone
            return e
        return new_constructor_app
    
    # inductive stuff
    @profile
    @typechecked
    def reduce_recursor(self, e : Expression) -> Optional[Expression]:
        # TODO: quotient
        #if (env().is_quot_initialized()) {
        #    if (optional<expr> r = quot_reduce_rec(e, [&](expr const & e) { return whnf(e); })) {
        #        return r;
        #    }
        #}
        # TODO: understand this

        # 1. unfold the application and get the recursor
        rec_fn, rec_args = unfold_app(e)
        if not isinstance(rec_fn, Const): return None
        
        rec_decl = self.environment.get_declaration_under_name(rec_fn.name)
        if not isinstance(rec_decl, Recursor): return None

        major_idx = rec_decl.get_major_idx()
        #dprint(f"major_idx {major_idx}")
        if major_idx >= len(rec_args): return None
        major = rec_args[major_idx]
        #dprint(f"major before {major}")

        #dprint(f"rec_decl {rec_decl}")
        if rec_decl.isK:
            #major = self.to_constructor_when_K(rec_decl, major)
            # TODO : what is going on here?
            warnings.warn("K-style recursion not fully implemented yet")

        #dprint(f"rec_decl {rec_decl.info.name}")
        #for i, arg in enumerate(rec_args):
        #    #dprint(f"arg {i} {arg}")
        #dprint(f"major {major}")

        major = self.whnf(major, clone=False, unfold_definition=True)
        if isinstance(major, NatLit):
            major = self.nat_lit_to_constructor(major)
        elif isinstance(major, StringLit):
            major = self.str_lit_to_constructor(major)
        else:
            major = self.to_constructor_when_structure(rec_decl.get_major_induct(), major)
        
        rule = rec_decl.get_recursion_rule(major)
        if rule is None: return None

        _, major_args = unfold_app(major)
        if len(major_args) < rule.num_fields: return None 
        if len(rec_fn.lvl_params) != len(rec_decl.info.lvl_params): return None
        rhs = substitute_level_params_in_expression(rule.value, level_zip(rec_decl.info.lvl_params, rec_fn.lvl_params)) # clones the rule.value

        # apply parameters, motives and minor premises from recursor application.
        rhs = fold_apps(rhs, rec_args[:rec_decl.num_params + rec_decl.num_motives + rec_decl.num_minors])
        #The number of parameters in the constructor is not necessarily
        #equal to the number of parameters in the recursor when we have
        #nested inductive types. 
        nparams = len(major_args) - rule.num_fields
        # apply fields from major premise
        selected_major_args = major_args[nparams: nparams + rule.num_fields]
        if len(selected_major_args) != rule.num_fields:
            raise PanicError("Major premise does not have the expected number of fields.")
        rhs = fold_apps(rhs, selected_major_args)
        if len(rec_args) > major_idx + 1:
            rhs = fold_apps(rhs, rec_args[major_idx + 1:])
        
        #dprint(f"rhs {rhs}")
        return rhs
    
    def whnf_fvar(self, fvar : FVar) -> Expression:
        fvar_val = self.get_value_of_fvar(fvar) # we do not clone the value of the fvar since get_value_of_fvar already clones it
        if fvar_val is None:
            return fvar
        else:
            return self.whnf(fvar_val, clone=False, unfold_definition=False) 

    def whnf_core(self, expr : Expression, clone : bool, cheap_proj : bool) -> Expression:
        if clone:
            expr = clone_expression(expr, use_same_fvars=True)
    
        if isinstance(expr, BVar) or isinstance(expr, Sort) or isinstance(expr, Pi) or isinstance(expr, Lambda) or isinstance(expr, NatLit) or isinstance(expr, StringLit) or isinstance(expr, Const): return expr
        elif isinstance(expr, FVar):
            if expr.is_let:
                pass
            else:
                return expr
        
        # TODO: caching
        r = None
        if isinstance(expr, FVar):
            return self.whnf_fvar(expr)
        elif isinstance(expr, Proj):
            pos_red = self.reduce_proj(expr, clone=False, cheap_proj=cheap_proj) 
            if pos_red is None:
                r = expr
            else:
                r = self.whnf_core(pos_red, clone=False, cheap_proj=cheap_proj)     
        elif isinstance(expr, App):
            raw_fn = get_app_function(expr)
            fn = self.whnf_core(raw_fn, clone=False, cheap_proj=cheap_proj)
            if isinstance(fn, Lambda):
                r = self.whnf_core(self.beta_reduction(expr, clone=False), clone=False, cheap_proj=cheap_proj)
            elif fn == raw_fn:
                #dprint(f"rr {expr}")
                r = self.reduce_recursor(expr)
                if r is not None: 
                    red = self.whnf_core(r, clone=False, cheap_proj=cheap_proj)
                    #dprint(f"red {red}")
                    return red
                else: return expr
            else:
                r = expr
        elif isinstance(expr, Let):
            r = self.whnf_core(self.zeta_reduction(expr, clone=False), clone=False, cheap_proj=cheap_proj)
        
        if r is None:
            raise PanicError(f"Expr of type {expr.__class__.__name__} could not be matched, this should not happen.")

        return r
    
    def whnf(self, expr : Expression, clone : bool, unfold_definition : bool) -> Expression:
        # TODO delta reduction
        expr = self.whnf_core(expr, clone=clone, cheap_proj=False)
        while unfold_definition:

            r_expr = self.reduce_nat_lit(expr, clone=True) # TODO : CLONE CHECKED
            if r_expr is not None: expr = r_expr
            else:
                unfolded = self.delta_reduction(expr, clone=False)
                if unfolded is None:
                    return expr
                expr = self.whnf_core(unfolded, clone=False, cheap_proj=False) # we do not clone the unfolded expression since the initial whnf_core already clones it
        return expr

    # TYPE INFERENCE
    def infer_fvar(self, fvar : FVar):
        return self.get_type_of_fvar(fvar)
        
    def infer_app(self, app : App, clone : bool, infer_only : bool) -> Expression: # CLONE CHECKED
        if infer_only: # CLONE CHECKED
            # if infer_only is true we only check that the type of fn is a pi type and keep substituting the arguments into the function type's body_type
            fn, args = unfold_app(app)
            fn_type = self.infer_core(fn, clone=clone, infer_only=infer_only)
            for arg in args:
                if not isinstance(fn_type, Pi):
                    fn_type = self.whnf(fn_type, clone=False, unfold_definition=True) # try whnfing to see if we can get a pi type

                    if not isinstance(fn_type, Pi):
                        raise ExpectedDifferentExpressionError(Pi, fn_type.__class__)
                
                fn_type = self.instantiate(
                    body=fn_type.body_type, 
                    val=arg, 
                    clone_body=False, # don't clone the body since we have (potentially) already cloned it using infer_core
                    clone_val=True
                )
            return fn_type
        else: # CLONE CHECKED
            # the function should be a pi type
            whnfd_fn_type = self.whnf(self.infer_core(app.fn, clone=clone, infer_only=infer_only), clone=False, unfold_definition=False)
            if not isinstance(whnfd_fn_type, Pi):
                raise ExpectedDifferentExpressionError(Pi, whnfd_fn_type.__class__)
            
            # get the type of the argument
            inferred_arg_type = self.infer_core(app.arg, clone=True, infer_only=infer_only)

            #has_fvar_not_in_context(inferred_arg_type, self.local_context) # TODO : remove this after testing
            #has_fvar_not_in_context(whnfd_fn_type.arg_type, self.local_context) # TODO : remove this after testing
            # the domain of the function should be equal to the type of the argument
            if not self.def_eq_core(whnfd_fn_type.arg_type, inferred_arg_type, clone=False):
                raise ExpectedDifferentTypesError(whnfd_fn_type.arg_type, inferred_arg_type)
            
            infered_type = self.instantiate(
                body=whnfd_fn_type.body_type, 
                val=app.arg,
                clone_body=False, # don't clone the body since we have (potentially) already cloned it using infer_core
                clone_val=True, # however, the argument should be cloned
            )
            return infered_type
            
    def infer_sort(self, sort : Sort, clone : bool) -> Expression:
        if clone:
            return Sort(LevelSucc(clone_level(sort.level)))
        return Sort(LevelSucc(sort.level))

    def infer_pi(self, pi : Pi, clone : bool, infer_only : bool) -> Expression:
        lhs = self.infer_sort_of(pi.arg_type, clone=True, infer_only=infer_only)

        fvar, inst_body_type = self.instantiate_fvar(
            bname=pi.bname, 
            arg_type=pi.arg_type, 
            arg_val=None,
            body=pi.body_type, 
            clone=clone
        )
        rhs = self.infer_sort_of(inst_body_type, clone=False, infer_only=False)
        self.remove_fvar(fvar)

        return Sort(LevelIMax(lhs, rhs))
    
    def infer_sort_of(self, e : Expression, clone : bool, infer_only : bool) -> Level:
        whnf_d_e_type = self.whnf(self.infer_core(e, clone=clone, infer_only=infer_only), clone=False, unfold_definition=True)
        if isinstance(whnf_d_e_type, Sort):
            return whnf_d_e_type.level
        raise ExpectedDifferentExpressionError(Sort, whnf_d_e_type.__class__)
    
    def infer_lambda(self, e : Lambda, clone : bool, infer_only : bool) -> Expression:
        if not infer_only:
            self.infer_sort_of(e.arg_type, clone=True, infer_only=True) # have to clone the arg_type since we are using it
        bname = e.bname
        fvar, inst_body = self.instantiate_fvar(
            bname=bname, 
            arg_type=e.arg_type, 
            arg_val=None,
            body=e.body, 
            clone=clone, 
        )
        infered_body_type = self.infer_core(inst_body, clone=False, infer_only=False)
        infered_pi = Pi(bname, e.arg_type, self.abstract(fvar, infered_body_type, clone=False, use_same_fvars=True))

        if has_specific_fvar(infered_pi, fvar): # TODO : remove this after testing
            raise PanicError("FVar was not abstracted in the inferred type.")

        return infered_pi
    
    def infer_const(self, c : Const) -> Expression:
        # this always clones the type from the environment
        return self.environment.get_constant_type(c)
    
    def infer_let(self, e : Let, clone : bool, infer_only : bool) -> Expression:
        if not infer_only:
            self.infer_sort_of(e.arg_type, clone=True, infer_only=infer_only) # have to clone the arg_type since we are using it 
            inferred_val_type = self.infer_core(e.val, clone=True, infer_only=infer_only) # have to clone the val since we are using it
            cloned_arg_type = clone_expression(e.arg_type, use_same_fvars=True) if clone else e.arg_type
            if not self.def_eq_core(inferred_val_type, cloned_arg_type, clone=False):
                raise ExpectedDifferentTypesError(inferred_val_type, cloned_arg_type)
        
        fvar, inst_body = self.instantiate_fvar( # we are using fvars since it is up to infer_core to unfold them if needed
            bname=e.bname, 
            arg_type=e.arg_type, 
            arg_val=e.val,
            body=e.body, 
            clone=clone, 
        )
        inferred_type = self.infer_core(inst_body, clone=False, infer_only=False)
        self.remove_fvar(fvar)

        if has_specific_fvar(inferred_type, fvar): # TODO : remove this after testing
            raise PanicError("FVar was not abstracted in the inferred type.")
        
        return inferred_type
    
    def proj_get_constructor(self, proj : Proj, clone : bool, infer_only : bool) -> Optional[Tuple[Const, InductiveType, Constructor, List[Expression]]]:
        """Returns the inductive type constant, the corresponding constructor, and the arguments to the constructor."""
        proj_name = proj.type_name
        struct_type = self.whnf(self.infer_core(proj.struct, clone=clone, infer_only=infer_only), clone=False, unfold_definition=True)
        inductive_fn, args = unfold_app(struct_type)
        if not isinstance(inductive_fn, Const): 
            #dprint(f"inductive_name {inductive_fn}")
            return None
        if inductive_fn.name != proj_name: 
            #dprint(f"inductive_name.name {inductive_fn.name}")
            return None
        
        inductive_decl = self.environment.get_inductive(inductive_fn.name)
        if inductive_decl.number_of_constructors() != 1: return None
        if len(args) != inductive_decl.num_params + inductive_decl.num_indices: return None
        
        constructor_decl = self.environment.get_constructor(inductive_decl.constructor_names[0]) # there is only one canonical constructor
        return inductive_fn, inductive_decl, constructor_decl, args

    def infer_proj(self, proj : Proj, clone : bool, infer_only : bool) -> Expression:
        proj_index = proj.index

        pos_cons = self.proj_get_constructor(proj, clone=True, infer_only=infer_only)
        if pos_cons is None: raise ProjectionError(f"Could not get constructor for projection {proj}")

        #I_name         I_infro          c_info        (in the original code)
        inductive_name, inductive_decl, constructor, args = pos_cons 
        constructor_type = self.environment.get_cloned_type_with_substituted_level_params(constructor, inductive_name.lvl_params)
        assert inductive_decl.num_params == constructor.num_params, "Sanity check failed: number of parameters in inductive type and constructor do not match."
        
        for i in range(inductive_decl.num_params):
            constructor_type = self.whnf(constructor_type, clone=False, unfold_definition=True)
            if not isinstance(constructor_type, Pi):
                raise ProjectionError(f"Expected a Pi type when reducing parameters for constructor type but got {constructor_type.__class__}")
            if i >= len(args):
                raise ProjectionError(f"Ran out of arguments for parameters when reducing constructor type.")
            
            constructor_type = self.instantiate(
                body=constructor_type.body_type, 
                val=args[i], 
                clone_body=False, 
                clone_val=True,
            )

        #is_prop_type = self.is_prop(constructor_type, clone=True) TODO: see next TODO
        for i in range(proj_index):
            constructor_type = self.whnf(constructor_type, clone=False, unfold_definition=False)
            if not isinstance(constructor_type, Pi):
                raise ProjectionError(f"Expected a Pi type when reducing indices for constructor type but got {constructor_type.__class__}")
            
            # TODO: the lean 4 code checks if the type has loose bvars, but how can this happen; if is_prop_type it then ensures that the body remains a prop
            if has_loose_bvars(constructor_type):
                raise PanicError("Loose bvars in constructor type")

            #dprint(f"1create proj with type_name {inductive_name.name}")
            constructor_type = self.instantiate(
                body=constructor_type.body_type,
                val=Proj(inductive_name.name, i, proj.struct), 
                clone_body=False, 
                clone_val=True
            )
        
        constructor_type = self.whnf(constructor_type, clone=False, unfold_definition=False)
        if not isinstance(constructor_type, Pi):
            raise ProjectionError(f"Expected a Pi type for projection index but got {constructor_type.__class__}")

        return constructor_type.arg_type

    def infer_nat_lit(self, n : NatLit) -> Expression:
        return Const(self.environment.Nat_name, [])
    
    def infer_string_lit(self, s : StringLit) -> Expression:
        return Const(self.environment.String_name, [])

    def infer_core(self, expr : Expression, clone : bool, infer_only : bool) -> Expression:
        """
        If check is true, we perform definitional equality checks (for example, the type of an
        argument to a lambda is the same type as the binder in the labmda). These checks
        are costly however, and in some cases we're using inference during reduction of
        expressions we know to be well-typed, so we can pass the flag `InferOnly` to omit
        these checks when they are not needed. (TODO change this comment)
        """
        has_fvar_not_in_context(expr, self.local_context) # TODO : remove this after testing

        #expr_class = expr.__class__

        if isinstance(expr, BVar): raise PanicError("BVar should have been substituted when inferring")
        elif isinstance(expr, FVar): inferred_type = self.infer_fvar(expr) # we should not clone the fvar since we are using "is" to compare
        elif isinstance(expr, App): inferred_type = self.infer_app(expr, clone=clone, infer_only=infer_only)
        elif isinstance(expr, Sort): inferred_type = self.infer_sort(expr, clone=clone)
        elif isinstance(expr, Const): inferred_type = self.infer_const(expr) # const always copies the type of the const from the environment
        elif isinstance(expr, Lambda): inferred_type = self.infer_lambda(expr, clone=clone, infer_only=infer_only)
        elif isinstance(expr, Pi): inferred_type = self.infer_pi(expr, clone=clone, infer_only=infer_only)
        elif isinstance(expr, Let): inferred_type = self.infer_let(expr, clone=clone, infer_only=infer_only)
        elif isinstance(expr, Proj): inferred_type = self.infer_proj(expr, clone=clone, infer_only=infer_only)
        elif isinstance(expr, NatLit): inferred_type = self.infer_nat_lit(expr) # this always inferred_type=s a new const
        elif isinstance(expr, StringLit): inferred_type = self.infer_string_lit(expr) # this always inferred_type=s a new const
        else: raise ValueError(f"Unknown expression type {expr.__class__.__name__}")
        
        has_fvar_not_in_context(inferred_type, self.local_context) # TODO : remove this after testing

        return inferred_type
    @profile
    @typechecked
    def infer(self, expr : Expression, clone : bool) -> Expression:
        if not self.local_context.is_empty():
            raise PanicError("Local context is not empty when inferring.")
        #rprint(f"CHECKING NEW EXPRESSION {expr}")
        inferred_type = self.infer_core(expr, clone=clone, infer_only=False)

        self.local_context.clear()

        has_fvar_not_in_context(inferred_type, self.local_context) # TODO : remove this after testing
        return inferred_type

    # CHECKING DECLARATIONS
    @profile
    @typechecked
    def check_declaration_info(self, info : DeclarationInfo):
        if not are_unique_level_params(info.lvl_params):
            raise EnvironmentError(f"Level parameters in declaration info {info} are not unique.")
        if has_fvars(info.type):
            raise EnvironmentError(f"Type in declaration info {info} contains free variables.")

        inferred_type = self.infer(info.type, clone=True)
        
        if not isinstance(inferred_type, Sort):
            raise EnvironmentError(f"Type of declaration info {info} is not a sort.")

    @profile
    @typechecked
    def add_definition(self, name : Name, d : Definition):
        #rprint(f"ADDING DEFINITION : {name}")
        self.check_declaration_info(d.info)

        infered_type = self.infer(d.value, clone=True)
        clone_d_info_type = clone_expression(d.info.type, use_same_fvars=True)
        if not self.def_eq_core(infered_type, clone_d_info_type, clone=False):
            raise DeclarationError(f"Definition {name} has type {d.info.type} but inferred type {infered_type}")
        self.environment.add_declaration(name, d)

        #rprint(f"ADDED DEFINITION : {name}")
        #rprint(f"INFO TYPE : {d.info.type}")
        #rprint(f"VALUE : {d.value}")
        #rprint(f"INFERRED TYPE : {infered_type}")
    
    @profile
    @typechecked
    def add_theorem(self, name : Name, t : Theorem):
        #rprint(f"ADDING THEOREM : {name}")
        self.check_declaration_info(t.info)

        infered_type = self.infer(t.value, clone=True)
        clone_t_info_type = clone_expression(t.info.type, use_same_fvars=True)
        if not self.def_eq_core(infered_type, clone_t_info_type, clone=False):
            raise DeclarationError(f"Theorem {name} has type {t.info.type} but inferred type {infered_type}")
        self.environment.add_declaration(name, t)

        #rprint(f"ADDED THEOREM : {name}")
    
    def add_opaque(self, name : Name, o : Opaque):
        #rprint(f"ADDING OPAQUE : {name}")
        self.check_declaration_info(o.info)

        inferred_type = self.infer(o.value, clone=True)
        clone_o_info_type = clone_expression(o.info.type, use_same_fvars=True)
        if not self.def_eq_core(inferred_type, clone_o_info_type, clone=False):
            raise DeclarationError(f"Opaque {name} has type {o.info.type} but inferred type {inferred_type}")
        
        self.environment.add_declaration(name, o)

        #rprint(f"ADDED OPAQUE : {name}")

    def add_axiom(self, name : Name, a : Axiom):
        #rprint(f"ADDING AXIOM : {name}")
        self.check_declaration_info(a.info)
        self.environment.add_declaration(name, a)

        #rprint(f"ADDED AXIOM : {name}")
    
    def add_inductive(self, name : Name, ind : InductiveType):
        #rprint(f"ADDING INDUCTIVE : {name}")
        #self.check_declaration_info(ind.info)
        assert name == ind.info.name, "Sanity check failed: name does not match info name."
        
        self.environment.add_declaration(name, ind)

        if not self.check_inductive_declaration_infos(name):
            raise DeclarationError(f"Inductive type {name} not well-formed.")
        #rprint(f"ADDED INDUCTIVE : {name}")

    def add_constructor(self, name : Name, constructor : Constructor):
        #rprint(f"ADDING CONSTRUCTOR: {name}")
        # Don't do this: self.check_declaration_info(constructor.info); see check_inductive_declaration_infos
        self.environment.add_declaration(name, constructor)

        #rprint(f"ADDED CONSTRUCTOR : {name}")

    def number_of_added_constructors(self, inductive_decl : InductiveType) -> int:
        count = 0
        for constructor_name in inductive_decl.constructor_names:
            if self.environment.exists_declaration_under_name(constructor_name):
                constructor_decl = self.environment.get_declaration_under_name(constructor_name)
                if not isinstance(constructor_decl, Constructor): raise DeclarationError(f"Inductive type's constructor name {inductive_decl.info.name} refers to a non-constructor {constructor_name}.")
                count += 1
        return count
    
    def check_inductive_declaration_infos(self, inductive : Name) -> bool:
        """
        Inductive types are special in that they are defined cyclically: the constructors and the inductive type refer to each other cyclically. Thus we cannot check them as they are added to the environment. Instead, we check them once each part of the inductive definition has been added to the environment.
        """
        self.environment.checking_inductive = True
        # First check that all the constructors have been added
        inductive_decl = self.environment.get_declaration_under_name(inductive)
        if not isinstance(inductive_decl, InductiveType):
            raise DeclarationError(f"Inductive type {inductive} not found.")
        
        found_constructors = self.number_of_added_constructors(inductive_decl)
        if found_constructors < inductive_decl.number_of_constructors(): return False
        assert(found_constructors == inductive_decl.number_of_constructors()), "Sanity check failed: number of found constructors does not match the number of expected constructors."

        self.check_declaration_info(inductive_decl.info)

        # Now check that the inductive type and its constructors are well-formed
        for constructor_name in inductive_decl.constructor_names:
            constructor_decl = self.environment.get_declaration_under_name(constructor_name)
            self.check_declaration_info(constructor_decl.info)
            assert isinstance(constructor_decl, Constructor), f"Sanity check failed: constructor {constructor_name} is not a constructor."

            if inductive_decl.num_params != constructor_decl.num_params:
                raise DeclarationError(f"Constructor {constructor_name} has {constructor_decl.num_params} parameters but the inductive type {constructor_decl.inductive_name} has {inductive_decl.num_params} parameters.")

        inductive_decl.is_checked = True
        for constructor_name in inductive_decl.constructor_names:
            constructor_decl = self.environment.get_declaration_under_name(constructor_name)
            assert isinstance(constructor_decl, Constructor), f"Sanity check failed: constructor {constructor_name} is not a constructor."
            constructor_decl.is_checked = True
        self.environment.checking_inductive = False
        return True

    def add_recursor(self, name : Name, recursor : Recursor):
        #rprint(f"ADDING RECURSOR : {name}")
        self.check_declaration_info(recursor.info)

        for rec_rule in recursor.recursion_rules:
            #rprint(f"ADDING RECURSOR RULE : {rec_rule}")
            #self.infer(rec_rule.value, clone=True)

            constructor_decl = self.environment.get_declaration_under_name(rec_rule.constructor)
            if not isinstance(constructor_decl, Constructor):
                raise DeclarationError(f"Recursor rule {rec_rule} is not associated with a constructor; found {constructor_decl.__class__.__name__} with name {constructor_decl.info.name} instead.")
            
            if constructor_decl.num_params != recursor.num_params:
                raise DeclarationError(f"Recursor rule {rec_rule} is associated with constructor {constructor_decl.info.name} which has {constructor_decl.num_params} parameters, but the recursor {recursor.info.name} has {recursor.num_params} parameters.")

        self.environment.add_declaration(name, recursor)

        #rprint(f"ADDED RECURSOR : {name}")

    def add_quotient(self, name : Name, q : Quot):
        #rprint(f"ADDING QUOTIENT : {name}")
        self.check_declaration_info(q.info)
        self.environment.add_declaration(name, q)

        #rprint(f"ADDED QUOTIENT : {name}")

    # adding declarations
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