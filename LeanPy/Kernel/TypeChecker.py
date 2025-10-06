from typing import List, Optional, Sequence, Tuple
from LeanPy.Kernel.Cache.Cache import InferCache, PairCache, WHNFCache # TODO: Pair cache is redundant, can be replace by map from tuple to value
from LeanPy.Kernel.Cache.EquivManager import EquivManager, FailureCache
from LeanPy.Kernel.KernelErrors import *
from LeanPy.Structures.Environment.Declarations.Declaration import Declaration, compare_reducibility_hints
from LeanPy.Structures.Environment.Environment import Environment
from LeanPy.Structures.Environment.LocalContext import LocalContext
from LeanPy.Structures.Environment.NatReduction import *
from LeanPy.Structures.Environment.NatReduction import is_nat_zero, is_nat_succ, is_nat_zero_const
from LeanPy.Structures.Environment.ReducibilityHint import Regular
from LeanPy.Structures.Expression.ExpressionManipulation import *
from LeanPy.Structures.Expression.LevelManipulation import *
from LeanPy.Structures.Name import Name
from LeanPy.Structures.Expression.Level import *
from LeanPy.Structures.Expression.Expression import *
from LeanPy.Structures.Environment.Declarations.Declaration import *

import sys
sys.setrecursionlimit(10**9)

#BIG TODO: go through sourcing one more time
# BIG TODO: check transitivity of source is preserved
class TypeChecker:
    def __init__(
            self, 
            allow_unstrict_infer : bool = True, # TODO: change this after testing
            environment : Environment | None = None,
            fun_on_successful_inference : Optional[Callable[[Expression, Expression], None]] = None,
            fun_on_successful_equality : Optional[Callable[[Expression, Expression], None]] = None,
        ):
        self.allow_unstrict_infer = allow_unstrict_infer

        self.whnf_cache = WHNFCache()
        self.whnf_core_cache = WHNFCache()
        self.infer_cache = [InferCache(), InferCache()]
        self.equiv_manager = EquivManager()
        self.failure_cache = FailureCache()
        self.instantiation_cache = PairCache[Expression, Expression, Expression]()
        self.instantiation_multiple_cache = PairCache[Expression, Tuple[Expression, ...], Expression]()
        self.lvl_param_subst_cache = PairCache[Tuple[Expression, Expression], Tuple[Tuple[LevelParam, Level], ...], Expression]()

        if environment is None:
            self.environment = Environment()
        else:
            self.environment = environment
        
        self.local_context = LocalContext()

        if fun_on_successful_inference is None:
            self.fun_on_successful_inference : Callable[[Expression, Expression], None] = lambda _s, _t : None
        else:
            self.fun_on_successful_inference = fun_on_successful_inference


        if fun_on_successful_equality is None:
            self.fun_on_successful_equality : Callable[[Expression, Expression], None] = lambda _s, _t : None
        else:
            self.fun_on_successful_equality = fun_on_successful_equality

    def remove_fvar(self, fvar: FVar):
        self.local_context.remove_fvar(fvar)

    def create_fvar(self, name: Name, type: Expression, val : Optional[Expression], is_let : bool, source : Optional[Any]) -> FVar:
        """
        Creates an FVar and adds it to the local context. It should have a value iff is_let is True.
        """
        copied_type = copy_expression(type, replace_source=source)
        copied_val = None if val is None else copy_expression(val, replace_source=source)
        fvar = FVar(name, type=copied_type, original_type=type, val=copied_val, original_val=val, is_let=is_let, source=source)
        self.local_context.add_fvar(fvar)
        return fvar
    
    def cleanup_fvars(self, fvars : List[FVar]):
        """
        Removes the fvars from the local context. Note that the fvars should be in the order of the outermost bound variable to the innermost bound variable.
        """
        for fvar in fvars[::-1]:
            self.remove_fvar(fvar)
    
    def get_type_of_fvar(self, fvar : FVar) -> Expression:
        """
        Returns the type of the fvar and makes sure that the fvar is in the local context.
        """
        return self.local_context.get_fvar_type(fvar)
    
    def get_value_of_fvar(self, fvar : FVar) -> Optional[Expression]:
        """
        Returns the value of the fvar and makes sure that the fvar is in the local context.
        """
        return self.local_context.get_fvar_value(fvar)
    
    def instantiate(self, body : Expression, val : Expression) -> Expression:
        """
        Replace the outermost bound variable in the body with the value. 
        IMPORTANT:
        - it does NOT do this in place, but instead creates new nodes when some of its children were replaced.
        """
        cached_inst_body = self.instantiation_cache.get(body, val)
        if cached_inst_body is not None: 
            return cached_inst_body

        inst_body = instantiate_bvar(body, val)
        if not body.has_mvars: # cache only if there are no metavariables in the body
            assert not inst_body.has_mvars
            self.instantiation_cache.put(body, val, inst_body)
        return inst_body

    def instantiate_multiple(self, body : Expression, vals : Sequence[Expression]) -> Expression:
        """
        Replace the outermost bound variables in the body with the values. 
        IMPORTANT:
        - it does NOT do this in place, but instead creates new nodes when some of its children were replaced,
        - vals should be in order of the innermost bound variable to the outermost bound variable.
        """
        vals_tuple = tuple(vals)
        cached_inst_body = self.instantiation_multiple_cache.get(body, vals_tuple)
        if cached_inst_body is not None: 
            return cached_inst_body

        inst_body = instantiate_bvars(body, vals_tuple)
        if not inst_body.has_mvars: # cache only if there are no metavariables in the instantiate body
            assert not body.has_mvars
            self.instantiation_multiple_cache.put(body, vals_tuple, inst_body)
        return inst_body
    
    def subst_level_params(self, expr : Expression, lvl_params : List[LevelParam], levels : List[Level], source : Optional[Any]) -> Expression:
        """
        Substitute the level parameters in the expression with the levels. Allows for caching.
        """
        lvl_subst = level_zip(lvl_params, levels)
        lvl_subst_tuple = tuple(lvl_subst)

        expr_source = expr.source if source is None else source
        cached_subst_expr = self.lvl_param_subst_cache.get((expr, expr_source), lvl_subst_tuple)
        if cached_subst_expr is not None: 
            return cached_subst_expr

        subst_expr = substitute_level_params_in_expression(expr, lvl_subst, replace_source=source)
        if not subst_expr.has_mvars: # cache only if there are no metavariables in the expression
            assert not expr.has_mvars
            self.lvl_param_subst_cache.put((expr, expr_source), lvl_subst_tuple, subst_expr)

        return subst_expr

    def check_level_params_length(self, decl : Declaration, subst : List[Level]):
        if len(decl.lvl_params) != len(subst):
            raise DeclarationError(f"""
            Declaration {decl.name} has {len(decl.lvl_params)} level parameters, but {len(subst)} levels were provided.

            Decl parameters : {[str(l) for l in decl.lvl_params]}
            Subs parameters : {[str(l) for l in subst]}
            """)
    
    def get_declaration_type_with_substituted_level_params(self, decl : Declaration, subs : List[Level], source : Optional[Any]) -> Expression:
        """
        Substitute the level parameters in the declaration type with the levels. 
        """
        self.check_level_params_length(decl, subs)
        return self.subst_level_params(decl.type, decl.lvl_params, subs, source=source)

    def get_declaration_val_with_substituted_level_params(self, decl : Definition | Theorem | Opaque, subs : List[Level], source : Optional[Any]) -> Expression:
        """
        Substitute the level parameters in the declaration value with the levels.
        """
        self.check_level_params_length(decl, subs)
        return self.subst_level_params(decl.value, decl.lvl_params, subs, source=source)
    
    def ensure_pi(self, expr : Expression, pi_source : Expression) -> Pi:
        """
        Ensures that the expression is a Pi type. If this is not immediate it tries reducing it using whnf. Throws an error if the expression is not a Pi type.
        """

        if isinstance(expr, MVar):
            raise UnfinishedExpressionError(expr.source)

        if isinstance(expr, Pi): 
            return expr
        
        whnfed_expr = self.whnf(expr)
        if  isinstance(whnfed_expr, Pi): 
            return whnfed_expr
        
        if isinstance(whnfed_expr, MVar):
            raise UnfinishedExpressionError(whnfed_expr.source)
        
        raise ExpectedEqualExpressionsConstructorsError(Pi, whnfed_expr.__class__, source=pi_source.source) # we use pi_source as the source of the error, since there is nothing inherently wrong with expr, but the application using it (technically pi_source is a misnomer)
    
    def ensure_sort(self, e : Expression, sort_source : Expression) -> Sort:
        """
        Ensures that the expression is a Sort. If this is not immediate it tries reducing it using whnf. Throws an error if the expression is not a Sort.
        """
        if isinstance(e, MVar):
            raise UnfinishedExpressionError(e.source)
        if isinstance(e, Sort): 
            return e
        whnfd_e = self.whnf(e)
        if isinstance(whnfd_e, Sort): 
            return whnfd_e

        if isinstance(whnfd_e, MVar):
            raise UnfinishedExpressionError(whnfd_e.source)
        
        raise ExpectedEqualExpressionsConstructorsError(Sort, whnfd_e.__class__, source=sort_source.source) # we use sort_source as the source of the error, since there is nothing inherently wrong with e, but the context in which it is used
    
    def is_structure_like(self, decl_name : Name, source : Optional[Any]) -> bool:
        """
        A structure is an inductive type with only on constructor, with no indices, and no recursive arguments.
        """
        decl = self.environment.get_declaration_under_name(decl_name, source=source)
        if not isinstance(decl, Inductive): 
            return False
        return decl.number_of_constructors == 1 and decl.num_indices == 0 and not decl.is_recursive
    
    def is_prop(self, e : Expression, cheap_rec : bool = False, cheap_proj : bool = False) -> bool:
        """
        Returns if an expressions is a proposition. A proposition is a type that is a sort with level 0.
        """
        if cheap_rec:
            inferred_type = self.whnf_core(self.infer_core(e, infer_only=(self.allow_unstrict_infer and True)), cheap_rec=cheap_rec, cheap_proj=cheap_proj)
        else:
            inferred_type = self.whnf(self.infer_core(e, infer_only=(self.allow_unstrict_infer and True)))

        if isinstance(inferred_type, MVar):
            raise UnfinishedExpressionError(inferred_type.source)
        
        if not isinstance(inferred_type, Sort):
            return False
        
        return is_equivalent(inferred_type.level, self.environment.level_zero, False)
    
    # DEFINITIONAL EQUALITY
    def def_eq_offset(self, t : Expression, s : Expression, expect_true : bool) -> Optional[bool]:
        """
        Checks if the expressions representing natural numbers are equal (either in NatLit form or as an application of Nat.zero or Nat.succ).
        """
        if is_nat_zero(self.environment, t) and is_nat_zero(self.environment, s):
            return True
        pred_t = is_nat_succ(self.environment, t)
        pred_s = is_nat_succ(self.environment, s)
        if (pred_t is not None) and (pred_s is not None):
            return self.def_eq_core(pred_t, pred_s, expect_true)
        return None

    def def_eq_sort(self, l : Sort, r : Sort, expect_true : bool) -> bool:
        """
        The sorts are definitonally equal if their levels are considered equivalent.
        """
        if l.level.has_mvars:
            raise UnfinishedExpressionError(l.level.source)
        if r.level.has_mvars:
            raise PanicError("Unfinished expression in right hand side of definitional equality.")
        
        ret = is_equivalent(l.level, r.level, expect_true=expect_true)
        if expect_true and not ret:
            raise PanicError(f"This should be unreachable")
        return ret
    
    def def_eq_const(self, l : Const, r : Const, expect_true : bool) -> bool:
        """
        If the names are the same, and the level parameters are equal, then the constants are equal.
        """
        if l.cname == r.cname:
            for lvl in l.lvl_params:
                if lvl.has_mvars:
                    raise UnfinishedExpressionError(lvl.source)
            for lvl in r.lvl_params:
                if lvl.has_mvars:
                    raise PanicError("Unfinished expression in right hand side of definitional equality.")

            if is_equivalent_list(l.lvl_params, r.lvl_params, expect_true): 
                return True
            #else: print(f"Constants {l} and {r} have the same name but different level parameters : {[str(lvl) for lvl in l.lvl_params]} and {[str(lvl) for lvl in r.lvl_params]}", file=sys.stderr)
        if expect_true:
            raise DefinitionalEqualityError(l, r)
        return False
    
    def def_eq_app(self, l : App, r : App, expect_true : bool) -> bool:
        """
        Check if the applications are equal by checking if the functions are definitionally equal and the arguments are definitionally equal.
        """
        f_fn, f_args, _ = unfold_app(l)
        g_fn, g_args, _ = unfold_app(r)
        if not self.def_eq(f_fn, g_fn, expect_true):
            return False
        
        if len(f_args) != len(g_args): 
            return False
        for f_arg, g_arg in zip(f_args, g_args):
            if not self.def_eq(f_arg, g_arg, expect_true):
                return False
        return True

    def def_eq_pi(self, init_t : Pi , init_s : Pi, expect_true : bool) -> bool:
        """
        Check if the Pis are equal by checking if the domains are equal (first it tries greedy structural equality, then it tries definitional equality) and then checking if the codomains are definitionally equal.
        """
        subs : List[FVar] = []
    
        t : Expression = init_t
        s : Expression = init_s
        while isinstance(t, Pi) and isinstance(s, Pi):
            var_s_type = None
            if not (t.domain == s.domain):
                var_s_type = self.instantiate_multiple(s.domain, subs[::-1])
                var_t_type = self.instantiate_multiple(t.domain, subs[::-1])
                if not self.def_eq(var_t_type, var_s_type, expect_true):
                    self.cleanup_fvars(subs)
                    return False
            if t.codomain.has_loose_bvars or s.codomain.has_loose_bvars:
                if var_s_type is None:
                    var_s_type = self.instantiate_multiple(s.domain, subs[::-1])
                subs.append(self.create_fvar(s.bname, var_s_type, val=None, is_let=False, source=None))
            else:
                subs.append(self.create_fvar(self.environment.filler_name, self.environment.filler_const, val=None, is_let=False, source=None))
            t = t.codomain
            s = s.codomain
        ret = self.def_eq(self.instantiate_multiple(t, subs[::-1]), self.instantiate_multiple(s, subs[::-1]), expect_true)

        self.cleanup_fvars(subs)

        return ret
    
    def def_eq_lambda(self, init_t : Lambda , init_s : Lambda, expect_true : bool) -> bool:
        """
        Check if the Lambdas are equal by checking if the domains are equal (first it tries greedy structural equality, then it tries definitional equality) and then checking if the bodies are definitionally equal.
        """

        subs : List[FVar] = []
    
        t : Expression = init_t
        s : Expression = init_s
        while isinstance(t, Lambda) and isinstance(s, Lambda):
            var_s_type = None
            if not (t.domain == s.domain):
                var_s_type = self.instantiate_multiple(s.domain, subs[::-1])
                var_t_type = self.instantiate_multiple(t.domain, subs[::-1])
                if not self.def_eq(var_t_type, var_s_type, expect_true):
                    self.cleanup_fvars(subs)
                    return False
            if t.body.has_loose_bvars or s.body.has_loose_bvars:
                if var_s_type is None:
                    var_s_type = self.instantiate_multiple(s.domain, subs[::-1])
                subs.append(self.create_fvar(s.bname, var_s_type, val=None, is_let=False, source=None))
            else:
                subs.append(self.create_fvar(self.environment.filler_name, self.environment.filler_const, val=None, is_let=False, source=None))
            t = t.body
            s = s.body
            
        ret = self.def_eq(self.instantiate_multiple(t, subs[::-1]), self.instantiate_multiple(s, subs[::-1]), expect_true)
        self.cleanup_fvars(subs)
        return ret

    def are_struct_eq_exprs(self, a : Expression, b : Expression, expect_true : bool, use_hash : bool) -> bool:
        """
        This function checks if two expressions are structurally equal OR if they have been found to be equal by the equivalence manager.
        """
        if isinstance(a, MVar):
            raise UnfinishedExpressionError(a.source)
        elif isinstance(b, MVar):
            raise PanicError("Unfinished expression in right side of definitional equality.")

        if a is b: 
            return True
        if use_hash and a.hash != b.hash:
            if expect_true:
                raise DefinitionalEqualityError(a, b)
            return False
        if isinstance(a, BVar) and isinstance(b, BVar): 
            ret = a.db_index == b.db_index
            if expect_true and not ret:
                raise DefinitionalEqualityError(a, b)
            return ret

        # check the equivalence manager
        if not a.has_mvars and not b.has_mvars:
            dsu_ra = self.equiv_manager.expr_to_dsu_root(a)
            dsu_rb = self.equiv_manager.expr_to_dsu_root(b)
            if dsu_ra is dsu_rb: 
                return True
        
        # fall back to structural equality
        if a.__class__ != b.__class__: 
            if expect_true:
                raise DefinitionalEqualityError(a, b)
            return False

        result = False
        if isinstance(a, BVar) and isinstance(b, BVar): raise PanicError("Unreachable code reached: BVar should have been handled by the first if statement.")
        elif isinstance(a, Const) and isinstance(b, Const): result = self.def_eq_const(a, b, expect_true=expect_true)
        #elif isinstance(a, MVar) and isinstance(b, MVar): result = (a is b)
        elif isinstance(a, FVar) and isinstance(b, FVar): result = (a is b)
        elif isinstance(a, App) and isinstance(b, App): result = self.are_struct_eq_exprs(a.fn, b.fn, use_hash=use_hash, expect_true=expect_true) and self.are_struct_eq_exprs(a.arg, b.arg, use_hash=use_hash, expect_true=expect_true)
        elif isinstance(a, Lambda) and isinstance(b, Lambda): result = self.are_struct_eq_exprs(a.domain, b.domain, use_hash=use_hash, expect_true=expect_true) and self.are_struct_eq_exprs(a.body, b.body, use_hash=use_hash, expect_true=expect_true)
        elif isinstance(a, Pi) and isinstance(b, Pi): result = self.are_struct_eq_exprs(a.domain, b.domain, use_hash=use_hash, expect_true=expect_true) and self.are_struct_eq_exprs(a.codomain, b.codomain, use_hash=use_hash, expect_true=expect_true)
        elif isinstance(a, Sort) and isinstance(b, Sort): result = self.def_eq_sort(a, b, expect_true=expect_true)
        elif isinstance(a, NatLit) and isinstance(b, NatLit): result = (a.val == b.val)
        elif isinstance(a, StrLit) and isinstance(b, StrLit): result = (a.val == b.val)
        # what about MData?
        elif isinstance(a, Proj) and isinstance(b, Proj): result = (a.index == b.index) and self.are_struct_eq_exprs(a.expr, b.expr, use_hash=use_hash, expect_true=expect_true)
        elif isinstance(a, Let) and isinstance(b, Let): result = self.are_struct_eq_exprs(a.domain, b.domain, use_hash=use_hash, expect_true=expect_true) and self.are_struct_eq_exprs(a.val, b.val, use_hash=use_hash, expect_true=expect_true) and self.are_struct_eq_exprs(a.body, b.body, use_hash=use_hash, expect_true=expect_true)
        else: raise PanicError(f"Unreachable code reached: Cannot compare expressions of class {a.__class__.__name__} and {b.__class__.__name__}.")
        
        if result:
            if not a.has_mvars and not b.has_mvars: # only add to the equivalence manager if there are no metavariables
                dsu_ra = self.equiv_manager.expr_to_dsu_root(a)
                dsu_rb = self.equiv_manager.expr_to_dsu_root(b)
                self.equiv_manager.add_equiv(dsu_ra, dsu_rb)

        if expect_true and not result:
            raise DefinitionalEqualityError(a, b)

        return result

    def def_eq_easy(self, l: Expression, r: Expression, expect_true : bool, use_hash : bool = False) -> Optional[bool]:
        """
        If the expressions are easily compared (Sort, BVar, Const, FVar, App, Lambda, Pi, NatLit, StrLit), then this function compares them. Otherwise, it returns None and expressions are compared using def_eq_core.
        """
        if self.are_struct_eq_exprs(l, r, expect_true=False, use_hash=use_hash): 
            return True

        if l.__class__ != r.__class__:
            if (isinstance(l, Pi) and isinstance(r, Sort)) or (isinstance(l, Sort) and isinstance(r, Pi)): # easy non-equality case
                if expect_true:
                    raise DefinitionalEqualityError(l, r)
                return False

            return None # not an easy case

        if isinstance(l, Sort) and isinstance(r, Sort): 
            return self.def_eq_sort(l, r, expect_true)
        elif isinstance(l, BVar) or isinstance(r, BVar): raise PanicError("BVar should have been substituted by now, when comparing expressions for definitional equality.")
        
        elif isinstance(l, Pi) and isinstance(r, Pi):
            return self.def_eq_pi(l, r, expect_true)
        elif isinstance(l, Lambda) and isinstance(r, Lambda):
            return self.def_eq_lambda(l, r, expect_true)
        elif isinstance(l, NatLit) and isinstance(r, NatLit): 
            ret = l.val == r.val
            if expect_true and not ret:
                raise DefinitionalEqualityError(l, r)
            return ret
        elif isinstance(l, StrLit) and isinstance(r, StrLit): 
            ret = l.val == r.val
            if expect_true and not ret:
                raise DefinitionalEqualityError(l, r)
            return ret

    def def_eq_proof_irrel(self, t : Expression, s : Expression, expect_true : bool) -> Optional[bool]:
        """ 
        Proof irrelevance support for propositions. If two expressions have equal types (i. e. proposition statements), and the types are proposition, then the expressions are considered equal. 
        """
        t_type = self.infer_core(t, infer_only=(self.allow_unstrict_infer and True))
        if not self.is_prop(t_type):
            return None
        s_type = self.infer_core(s, infer_only=(self.allow_unstrict_infer and True))
        return self.def_eq(t_type, s_type, expect_true)
    
    def def_eq_unit_like(self, t : Expression, s : Expression, expect_true : bool) -> bool:
        """
        If the expressions are both of a structure with no fields, then they are equal if their types are equal.
        """

        t_type = self.whnf(self.infer_core(t, infer_only=(self.allow_unstrict_infer and True)))
        inductive_const = get_app_function(t_type)

        if not isinstance(inductive_const, Const):
            if expect_true:
                raise DefinitionalEqualityError(t, s)
            return False
        if not self.is_structure_like(inductive_const.cname, source=inductive_const.source): 
            if expect_true:
                raise DefinitionalEqualityError(t, s)
            return False

        constructor = self.get_first_constructor(inductive_const.cname, inductive_name_source=inductive_const.source)
        if constructor is None:
            if expect_true:
                raise DefinitionalEqualityError(t, s)
            return False
        if constructor.num_fields != 0:
            if expect_true:
                raise DefinitionalEqualityError(t, s) 
            return False
        return self.def_eq_core(t_type, self.infer_core(s, infer_only=(self.allow_unstrict_infer and True)), expect_true)
    
    def def_eq_core(self, l : Expression, r : Expression, expect_true : bool) -> bool:
        ret = self.def_eq_core_logic(l, r, expect_true)
        if ret: 
            self.fun_on_successful_equality(l, r)
        
        return ret

    def def_eq_core_logic(self, l : Expression, r : Expression, expect_true : bool) -> bool:
        """
        The main function for checking definitional equality. It tries to compare the expressions in multiple stages:
        1. It tries to compare in the easy cases (see def_eq_easy)
        2. If the expressions are not easily compared, then they are reduced to weak head normal form and compared.
        3. proof irrelevance is tried
        4. lazy delta reduction is tried (reducing the expressions by unfolding definitions and compares when it looks promising)
        5. If the expressions are constants, fvars, or projections, then they are compared naively.
        6. They are more strongly reduced to weak head normal by also reducing projections and compared.
        7. If the expressions are applications, then they are compared by comparing the functions and the arguments.
        8. eta expansion is tried
        9. structural eta expansion is tried
        10. unit-like structures are compared
        Finally, if none of the above steps return a definitive answer, then they are not considered equal (although in easy cases, the negative answer might be returned earlier).
        """
        if isinstance(l, MVar):
            raise UnfinishedExpressionError(l.source)
        elif isinstance(r, MVar):
            raise PanicError("Unfinished expression in right side of definitional equality.")

        is_easy = self.def_eq_easy(l, r, expect_true=expect_true, use_hash=True)
        if is_easy is not None:
            assert not (expect_true and not is_easy), f"This should be unreachable"
            return is_easy

        if not l.has_fvars and isinstance(r, Const) and r == Const(cname=self.environment.Bool_true_name, lvl_params=[], source=None):
            whnfd_l = self.whnf(l)
            if isinstance(whnfd_l, Const) and whnfd_l == Const(cname=self.environment.Bool_true_name, lvl_params=[], source=None):
                return True

        l_n = self.whnf_core(l, cheap_rec=False, cheap_proj=True)
        r_n = self.whnf_core(r, cheap_rec=False, cheap_proj=True)

        if isinstance(l_n, MVar):
            raise UnfinishedExpressionError(l.source)
        elif isinstance(r_n, MVar):
            raise PanicError("Unfinished expression in right side of definitional equality.")
     
        if (l_n is not l) or (r_n is not r):
            is_easy = self.def_eq_easy(l_n, r_n, expect_true)
            if is_easy is not None:
                assert not (expect_true and not is_easy), f"This should be unreachable"
                return is_easy

        is_proof_irr = self.def_eq_proof_irrel(l_n, r_n, expect_true)
        if is_proof_irr is not None:
            assert not (expect_true and not is_proof_irr), f"This should be unreachable"
            return is_proof_irr

        l_n_n, r_n_n, try_lazy = self.lazy_delta_reduction(l_n, r_n, expect_true=False)
        if isinstance(l_n_n, MVar):
            raise UnfinishedExpressionError(l.source)
        elif isinstance(r_n_n, MVar):
            raise PanicError("Unfinished expression in right side of definitional equality.")
        
        if try_lazy is not None:
            if expect_true and not try_lazy:
                raise DefinitionalEqualityError(l, r)
            return try_lazy

        if isinstance(l_n_n, Const) and isinstance(r_n_n, Const):
            if self.def_eq_const(l_n_n, r_n_n, False): 
                return True
        if isinstance(l_n_n, FVar) and isinstance(r_n_n, FVar) and (l_n_n is r_n_n): 
            return True
        if isinstance(l_n_n, Proj) and isinstance(r_n_n, Proj) and l_n_n.index == r_n_n.index:
            if self.lazy_delta_proj_reduction(l_n_n.expr, r_n_n.expr, l_n_n.index, expect_true=False):
                return True

        l_n_n_n = self.whnf_core(l_n_n, cheap_rec=False, cheap_proj=False) # don't use cheap_proj now
        r_n_n_n = self.whnf_core(r_n_n, cheap_rec=False, cheap_proj=False) # don't use cheap_proj now

        if isinstance(l_n_n_n, MVar):
            raise UnfinishedExpressionError(l.source)
        elif isinstance(r_n_n_n, MVar):
            raise PanicError("Unfinished expression in right side of definitional equality.")

        if (l_n_n_n is not l_n_n) or (r_n_n_n is not r_n_n): 
            return self.def_eq_core(l_n_n_n, r_n_n_n, expect_true)

        if isinstance(l_n_n_n, App) and isinstance(r_n_n_n, App):
            if self.def_eq_app(l_n_n_n, r_n_n_n, expect_true=False): 
                return True

        # Try reductions
        if self.try_eta_expansion(l_n_n_n, r_n_n_n, expect_true=False):
            return True
        if self.try_structural_eta_expansion(l_n_n_n, r_n_n_n, expect_true=False):
            return True
        
        try_lit_expansion = self.try_string_lit_expansion(l_n_n_n, r_n_n_n, expect_true)
        if try_lit_expansion is not None:
            assert not (expect_true and not try_lit_expansion), f"This should be unreachable"
            return try_lit_expansion

        if self.def_eq_unit_like(l_n_n_n, r_n_n_n, expect_true=False): 
            return True
        
        if expect_true:
            raise DefinitionalEqualityError(l, r)

        return False
    
    def def_eq(self, l: Expression, r: Expression, expect_true : bool) -> bool:
        """
        Same as def_eq_core, but also adds the expressions to the equivalence manager if they are equal.
        """
        ret = self.def_eq_core(l, r, expect_true)
        if ret: 
            if not l.has_mvars and not r.has_mvars: # only add to the equivalence manager if there are no metavariables
                self.equiv_manager.add_equiv_expressions(l, r)
        return ret

    # EXPANSIONS
    def try_eta_expansion_core(self, t : Expression, s : Expression, expect_true : bool) -> bool:
        """
        Tries to eta expand s: if s is a function, then by eta expansion, it is equal to the expression "fun x => s x". This is not symmetric.
        """
        if not (isinstance(t, Lambda) and (not isinstance(s, Lambda))):
            if expect_true:
                raise DefinitionalEqualityError(t, s)
            return False
        
        s_type = self.whnf(self.infer_core(s, infer_only=(self.allow_unstrict_infer and False)))
        if not isinstance(s_type, Pi): 
            if expect_true:
                raise DefinitionalEqualityError(t, s)
            return False
        new_s = Lambda(bname=s_type.bname, domain=s_type.domain, body=App(s, BVar(0, source=None), source=None), source=None)
        return self.def_eq(t, new_s, expect_true)
    
    def try_eta_expansion_core_antisymm(self, t : Expression, s : Expression, expect_true : bool) -> bool:
        """ Same as try_eta_expansion_core, but roles of t and s are reversed. """
        if not (isinstance(s, Lambda) and (not isinstance(t, Lambda))):
            if expect_true:
                raise DefinitionalEqualityError(t, s)
            return False
        
        t_type = self.whnf(self.infer_core(t, infer_only=(self.allow_unstrict_infer and False)))
        if not isinstance(t_type, Pi): 
            if expect_true:
                raise DefinitionalEqualityError(t, s)
            return False
        new_t = Lambda(bname=t_type.bname, domain=t_type.domain, body=App(t, BVar(0, source=None), source=None), source=None)
        return self.def_eq(new_t, s, expect_true)
    
    def try_eta_expansion(self, t : Expression, s : Expression, expect_true : bool) -> bool:
        """
        Tries to eta expand y and compares it to x, then tries to eta expand x and compares it to y. 
        """
        ret = self.try_eta_expansion_core(t, s, expect_true=False) or self.try_eta_expansion_core_antisymm(t, s, expect_true=False)
        if expect_true and not ret:
            raise DefinitionalEqualityError(t, s)
        return ret
    
    def try_structural_eta_expansion_core(self, t : Expression, s : Expression, expect_true : bool) -> bool:
        """
        If the t and s are applications of a constructor of a structure, then they are equal if the types are equal and the arguments are equal. This is done non-symmetrically: arguments of s are compared to projections of t (the projections then correspond to the arguments of t).
        """

        # First part: deconstruct s, ensure it is an application of a constructor
        s_fn, s_args, _ = unfold_app(s)

        if not isinstance(s_fn, Const):
            if expect_true:
                raise DefinitionalEqualityError(t, s) 
            return False
        
        # NOTE: providing source cannot lead to higher-up leaks since decl is not used in any inference function
        decl = self.environment.get_declaration_under_name(s_fn.cname, source=s_fn.source)
        if not isinstance(decl, Constructor): 
            if expect_true:
                raise DefinitionalEqualityError(t, s)
            return False

        # Second part: ensure that the application has the correct number of arguments and that the inductive type is a structure
        if len(s_args) != decl.num_params + decl.num_fields: 
            if expect_true:
                raise DefinitionalEqualityError(t, s)
            return False
        if not self.is_structure_like(decl.inductive_name, source=s_fn.source): 
            if expect_true:
                raise DefinitionalEqualityError(t, s)
            return False

        # Third part: ensure that the types are equal
        if not self.def_eq(
            self.infer_core(t, infer_only=(self.allow_unstrict_infer and True)),
            self.infer_core(s, infer_only=(self.allow_unstrict_infer and True)),
            expect_true
        ): 
            assert not expect_true, f"This should be unreachable"
            return False

        # Fourth part: ensure that the arguments are equal:
        # s was decomposed, so we know the arguments
        # for t we don't know the arguments, so we use proj to get them
        for i in range(decl.num_params, len(s_args)):
            # NOTE: Use None source to avoid higher-up leaks
            t_i_proj = Proj(sname=decl.inductive_name, index=i-decl.num_params, expr=t, source=None)

            # compare the arguments
            if not self.def_eq(t_i_proj, s_args[i], expect_true):
                assert not expect_true, f"This should be unreachable"
                return False
        return True
    
    def try_structural_eta_expansion_core_antisymm(self, t : Expression, s : Expression, expect_true : bool) -> bool:
        """
        If the t and s are applications of a constructor of a structure, then they are equal if the types are equal and the arguments are equal. This is done non-symmetrically: arguments of s are compared to projections of t (the projections then correspond to the arguments of t).
        """

        # First part: deconstruct s, ensure it is an application of a constructor
        t_fn, t_args, _ = unfold_app(t)

        if not isinstance(t_fn, Const):
            if expect_true:
                raise DefinitionalEqualityError(t, s) 
            return False
        
        decl = self.environment.get_declaration_under_name(t_fn.cname, source=t_fn.source)
        if not isinstance(decl, Constructor): 
            if expect_true:
                raise DefinitionalEqualityError(t, s)
            return False

        # Second part: ensure that the application has the correct number of arguments and that the inductive type is a structure
        if len(t_args) != decl.num_params + decl.num_fields: 
            if expect_true:
                raise DefinitionalEqualityError(t, s)
            return False
        if not self.is_structure_like(decl.inductive_name, source=t_fn.source): 
            if expect_true:
                raise DefinitionalEqualityError(t, s)
            return False

        # Third part: ensure that the types are equal
        if not self.def_eq(
            self.infer_core(t, infer_only=(self.allow_unstrict_infer and True)),
            self.infer_core(s, infer_only=(self.allow_unstrict_infer and True)),
            expect_true
        ): 
            assert not expect_true, f"This should be unreachable"
            return False

        # Fourth part: ensure that the arguments are equal:
        # s was decomposed, so we know the arguments
        # for t we don't know the arguments, so we use proj to get them
        for i in range(decl.num_params, len(t_args)):
            # NOTE: same note as in try_structural_eta_expansion_core
            s_i_proj = Proj(sname=decl.inductive_name, index=i-decl.num_params, expr=s, source=None)

            # compare the arguments
            if not self.def_eq(t_args[i], s_i_proj, expect_true):
                assert not expect_true, f"This should be unreachable"
                return False
        return True
    
    def try_structural_eta_expansion(self, t : Expression, s : Expression, expect_true : bool) -> bool:
        """
        Tries to eta expand s and compares it to t, then tries to eta expand t and compares it to s. 
        """
        ret = self.try_structural_eta_expansion_core(t, s, expect_true=False) or self.try_structural_eta_expansion_core_antisymm(t, s, expect_true=False)
        if expect_true and not ret:
            raise DefinitionalEqualityError(t, s)
        return ret
    
    def try_string_lit_expansion_core(self, t : Expression, s : Expression, expect_true : bool) -> Optional[bool]:
        if isinstance(t, StrLit) and isinstance(s, App) and get_app_function(s) == Const(self.environment.String_mk_name, [], source=None):
            return self.def_eq_core(str_lit_to_constructor(self.environment, t), s, expect_true)
        return None
    
    def try_string_lit_expansion_core_antisymm(self, t : Expression, s : Expression, expect_true : bool) -> Optional[bool]:
        if isinstance(s, StrLit) and isinstance(t, App) and get_app_function(t) == Const(self.environment.String_mk_name, [], source=None):
            return self.def_eq_core(t, str_lit_to_constructor(self.environment, s), expect_true)
        return None

    def try_string_lit_expansion(self, t : Expression, s : Expression, expect_true : bool) -> Optional[bool]:
        r = self.try_string_lit_expansion_core(t, s, expect_true=False)
        if r is not None: 
            if expect_true and not r:
                raise DefinitionalEqualityError(t, s)
            return r
        ret = self.try_string_lit_expansion_core_antisymm(t, s, expect_true=False)
        if ret is not None:
            if expect_true and not ret:
                raise DefinitionalEqualityError(t, s)
        return ret

    # CONSTRUCTORS
    def get_constructor(self, constructor_name : Name, source : Expression) -> Constructor:
        """
        Ensures that the declaration under the name is a constructor and returns it.
        """
        decl = self.environment.get_declaration_under_name(constructor_name, source=source.source)
        if not isinstance(decl, Constructor):
            raise DeclarationError(f"Name {constructor_name} is not a constructor.")
        return decl
    
    def expand_eta_struct(self, e_type : Expression, e : Expression):
        """
        Tries to eta expand the expression e: it gets the first constructor of the structure, and then constructs the application of the constructor with the arguments replaced by projections of e to corresponding fields.
        """
        fn, args, arg_sources = unfold_app(e_type)
        if not isinstance(fn, Const): 
            return e

        constructor = self.get_first_constructor(fn.cname, inductive_name_source=fn.source)
        if not constructor: 
            return e

        if len(args) < constructor.num_params:
            raise StructureError(f"Expected {constructor.num_params} parameters, but got {len(args)}.", source=e_type.source)
        args = args[:constructor.num_params]
        arg_sources = arg_sources[:constructor.num_params]
        result = fold_apps(Const(cname=constructor.name, lvl_params=fn.lvl_params, source=None), args, sources=arg_sources)
        result = fold_apps(result, [Proj(sname=fn.cname, index=i, expr=e, source=None) for i in range(constructor.num_fields)], sources=[None]*constructor.num_fields)
        return result

    def to_constructor_when_structure(self, inductive_name : Name, e : Expression, inductive_name_source : Expression, cheap_rec : bool, cheap_proj : bool) -> Expression:
        """
        If e is an instance of a structure A, but is not seen be to created using the constructor of A, then this function tries to convert e to the application of the (only) constructor of A.
        """
        if not self.is_structure_like(inductive_name, source=inductive_name_source): 
            return e

        f = get_app_function(e)
        if isinstance(f, Const) and isinstance(self.environment.get_declaration_under_name(f.cname, source=f.source), Constructor): 
            return e

        e_type = self.whnf_core(self.infer_core(e, infer_only=(self.allow_unstrict_infer and True)), cheap_rec=cheap_rec, cheap_proj=cheap_proj) if cheap_rec else self.whnf(self.infer_core(e, infer_only=(self.allow_unstrict_infer and True)))

        e_type_fn = get_app_function(e_type)
        if not (isinstance(e_type_fn, Const) and e_type_fn.cname == inductive_name): 
            return e 

        if self.is_prop(e_type, cheap_rec=cheap_rec, cheap_proj=cheap_proj): 
            return e
        return self.expand_eta_struct(e_type, e)

    def get_first_constructor(self, inductive_name : Name, inductive_name_source : Expression) -> Optional[Constructor]:
        """
        Gets the first constructor of the inductive type.
        """
        decl = self.environment.get_declaration_under_name(inductive_name, source=inductive_name_source)
        if not isinstance(decl, Inductive): 
            return None
        if decl.number_of_constructors == 0: 
            return None
        return self.get_constructor(decl.constructor_names[0], source=inductive_name_source)
    
    def mk_nullary_constructor(self, type_e : Expression, num_params : int) -> Optional[Expression]:
        """
        Auxiliary function for to_constructor_when_K. It constructs the application of the constructor of the inductive type supporting K-axiom. It replaces the arguments of the type with that of the constructor. The main use case is for Eq type, see comments in to_constructor_when_K.
        """
        d, args, arg_sources = unfold_app(type_e)
        if not isinstance(d, Const): 
            return None
        constructor = self.get_first_constructor(d.cname, inductive_name_source=d.source)
        if constructor is None: 
            return None
        if len(args) < num_params:
            raise StructureError(f"Expected at least {num_params} parameters, but got {len(args)}.", source=type_e.source)
        args = args[:num_params]
        arg_sources = arg_sources[:num_params]
        return fold_apps(Const(cname=constructor.name, lvl_params=d.lvl_params, source=d.source), args, sources=arg_sources)

    def to_constructor_when_K(self, recursor : Recursor, e : Expression, cheap_rec : bool, cheap_proj : bool) -> Expression:
        """
        See https://stackoverflow.com/questions/39239363/what-is-axiom-k
        For datatypes that support K-axiom, given `e` an element of that type, we convert (if possible)
        to the default constructor. For example, if `e : a = a`, then this method returns `eq.refl a` 
        """
        if not recursor.isK:
            raise PanicError("Cannot apply K-axiom to a recursor that is not K.")
        app_type = self.infer_core(e, infer_only=(self.allow_unstrict_infer and True))
        app_type = self.whnf_core(app_type, cheap_rec=cheap_rec, cheap_proj=cheap_proj) if cheap_rec else self.whnf(app_type)
        app_type_inductive, app_type_args, _ = unfold_app(app_type) # get the arguments of the type

        if not isinstance(app_type_inductive, Const): 
            return e
        if app_type_inductive.cname != recursor.get_major_induct(): # type of the major premise for the recursor should be the inductive type of the application
            return e

        # special handling of mvars
        if app_type.has_expr_mvars:
            # if app_type has mvars, then we can apply K-axiom only if all the arguments are mvar-free
            for i in range(recursor.num_params, len(app_type_args)):
                if app_type_args[i].has_expr_mvars:
                    return e

        # convert the expression to the application of the (only) constructor
        new_constructor_app = self.mk_nullary_constructor(app_type, recursor.num_params)
        if not new_constructor_app: 
            return e
        new_type = self.infer_core(new_constructor_app, infer_only=(self.allow_unstrict_infer and True))

        # ensure that the type is preserved after the conversion
        if not self.def_eq(app_type, new_type, expect_true=False): 
            return e
        return new_constructor_app
    
    # REDUCTIONS

    def cheap_beta_reduce(self, e : Expression) -> Expression:
        """
        Tries to naively simplify the expression by removing the arguments that are not used in the body of the lambdas.
        """
        if not isinstance(e, App): 
            return e
        fn, args, arg_sources = unfold_app(e)
        if not isinstance(fn, Lambda):
            return e
        
        i = 0
        while isinstance(fn, Lambda) and i < len(args):
            i += 1
            fn = fn.body
        
        if not fn.has_loose_bvars:
            return fold_apps(fn, args[i:], sources=arg_sources[i:])
        elif isinstance(fn, BVar): # the body is a single bound variable, so just replace it with the value of it args[i - fn.db_index - 1]
            if i <= fn.db_index:
                raise UnboundVariableError(f"Unbound variable in the body of the lambda.", source=fn.source)
            return fold_apps(args[i - fn.db_index - 1], args[i:], sources=arg_sources[i:]) # fold back the rest of the arguments
        else:
            return e

    def beta_reduction(self, 
            f : Expression, #  ( ... ((f a_1) a_2) ... a_n -> f, [a_1, a_2, ..., a_n] outermost to innermost
            args : List[Expression],
            args_sources : List[Expression]
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
        rest_arg_sources = args_sources[n_successful_subs:]
        successful_args = args[:n_successful_subs][::-1]
        
        inst_f = self.instantiate_multiple(f, successful_args)

        return fold_apps(inst_f, rest_args, sources=rest_arg_sources)
    
    def is_delta(self, expr : Expression) -> Optional[Tuple[Const, Definition | Opaque | Theorem, List[Expression], List[Expression]]]:
        """
        Checks if the expression is delta reducible: if it is an application of a declaration, then it returns the Constant referring to the declaration, the declaration, and the arguments. Otherwise, it returns None.

        Args:
            expr : Expression
                The expression to check if it is delta reducible.
            
        Returns:
            Optional[Tuple[Const, Definition | Opaque | Theorem, List[Expression]]]
                If the expression is delta reducible, then it returns the Constant referring to the declaration, the declaration, and the arguments. Otherwise, it returns None.

        """
        fn, args, arg_sources = unfold_app(expr)
        if not isinstance(fn, Const): 
            return None
        decl = self.environment.get_declaration_under_name(fn.cname, source=fn.source)
        if not decl.has_value(): 
            return None
        if not (isinstance(decl, Definition) or isinstance(decl, Opaque) or isinstance(decl, Theorem)):
            raise DeclarationError(f"Declaration {fn.cname} is not a Definition, Opaque, or Theorem.")
        return fn, decl, args, arg_sources
    
    def delta_reduction_core(self, fn : Const, decl : Definition | Opaque | Theorem, args : List[Expression], arg_sources: List[Expression]) -> Expression:
        """
        Unfold the definition of the declaration and folds back the arguments.

        Args:
            fn : Const
                The constant referring to the declaration.
            decl : Definition | Opaque | Theorem
                The declaration to unfold.
            args : List[Expression]
                The arguments of the application.

        Returns:
            Expression
                The expression after the delta reduction.
        """
        decl_val = self.get_declaration_val_with_substituted_level_params(decl, fn.lvl_params, source=None)
        return fold_apps(decl_val, args, sources=arg_sources)
    
    def delta_reduction(self, expr : Expression) -> Optional[Expression]:
        """ 
        Checks if the function of the application expr is a constant that can be unfolded, and if so, unfolds it.
        """
        is_d = self.is_delta(expr)
        if is_d is None: 
            return None
        ret = self.delta_reduction_core(*is_d)
        return ret
    
    def reduce_proj_core(self, proj_struct : Expression, idx : int) -> Optional[Expression]:
        """ 
        If we have a projection of an expression that is an application of a constructor, then we reduce it to the corresponding argument of the constructor. 
        
        For example, proj 0 (Prod.mk (A) (B) (a : A) (b : B)) would be reduced to a. Note that in this case A B are parameters of the constructor, and a and b are the actual arguments, used in the projection.
        """
        if isinstance(proj_struct, StrLit): proj_struct = str_lit_to_constructor(self.environment, proj_struct)
        
        proj_struct_fn, proj_struct_args, _ = unfold_app(proj_struct)
        if not isinstance(proj_struct_fn, Const): 
            return None
        # NOTE: decl not used in any inference function, so providing source cannot lead to higher-up leaks
        constructor_decl = self.environment.get_declaration_under_name(proj_struct_fn.cname, source=proj_struct_fn.source)
        if not isinstance(constructor_decl, Constructor): 
            return None

        if constructor_decl.num_params + idx >= len(proj_struct_args): 
            return None

        return proj_struct_args[constructor_decl.num_params + idx]
    
    def reduce_proj(self, proj : Proj, cheap_rec : bool, cheap_proj : bool) -> Optional[Expression]:
        """
        Reduces the projection by whnf-ing the expression and then checking the index-th argument using reduce_proj_core.
        """
        idx = proj.index
        c = proj.expr
        # use whnf to unfold the definitions if cheap_proj is False
        c = self.whnf_core(c, cheap_rec=cheap_rec, cheap_proj=cheap_proj) if cheap_proj else self.whnf(c) 
        return self.reduce_proj_core(c, idx)
    
    def try_unfold_proj_app(self, e : Expression) -> Optional[Expression]: 
        """
        If the expression is an application of a projection, then it tries to reduce it using whnf_core, used only in lazy_delta_reduction_step.
        """
        f = get_app_function(e)
        if not isinstance(f, Proj): 
            return None
        e_new = self.whnf_core(e, cheap_rec=False, cheap_proj=False)
        if e_new == e: 
            return None
        return e_new
    
    def def_eq_args(self, t : Expression, s : Expression, expect_true : bool) -> bool:
        """
        Compares the arguments of the applications t and s.
        """
        while isinstance(t, App) and isinstance(s, App):
            if not self.def_eq(t.arg, s.arg, expect_true): 
                assert not expect_true, f"This should be unreachable"
                return False
            t = t.fn
            s = s.fn
        ret = (not isinstance(t, App)) and (not isinstance(s, App))
        if expect_true and not ret:
            raise DefinitionalEqualityError(t, s)
        return ret

    def lazy_delta_reduction_step(self, t_n : Expression, s_n : Expression) -> Tuple[Expression, Expression, ReductionStatus]:
        """
        Tries to unfold the definitions of the function of the applications t_n and s_n, and compare the results. This is done in a lazy way: it tries to compare the expressions if they can be compared easily, and if not, then it unfolds the definitions and compares the results. Priorities are given to unfolding application where the function is a projection. If both t_n and s_n are definitions to be unfolded it first unfold the one which has a more pressing reducibility hint. If both have the same reducibility hint, then it unfolds both.

        Args:
            t_n : Expression
                The first expression to compare.
            s_n : Expression
                The second expression to compare.
        
        Returns:
            Tuple[Expression, Expression, ReductionStatus]
                The expressions after the reduction, and the status of the reduction.
        """
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
            if t_new is not None: t_n = t_new
            else: s_n = self.whnf_core(self.delta_reduction_core(*id_s), cheap_rec=False, cheap_proj=True)
        elif (id_t is not None) and (id_s is not None):
            hint_compare = compare_reducibility_hints(id_t[1], id_s[1])
            if hint_compare < 0: # reduce t
                t_n = self.whnf_core(self.delta_reduction_core(*id_t), cheap_rec=False, cheap_proj=True)
            elif hint_compare > 0: # reduce s
                s_n = self.whnf_core(self.delta_reduction_core(*id_s), cheap_rec=False, cheap_proj=True)
            else: # reduce both
                if isinstance(t_n, App) and isinstance(s_n, App) and (id_t[1] is id_s[1]) and isinstance(id_t[1], Definition) and isinstance(id_t[1].hint, Regular):
                    if not self.failure_cache.did_fail_before(t_n, s_n):
                        if self.def_eq_const(id_t[0], id_s[0], expect_true=False) and self.def_eq_args(t_n, s_n, expect_true=False):
                            return t_n, s_n, ReductionStatus.EQUAL
                        else:
                            if not t_n.has_mvars and not s_n.has_mvars: # if there are no mvars, then we can cache the failure
                                self.failure_cache.put(t_n, s_n)
                t_n = self.whnf_core(self.delta_reduction_core(*id_t), cheap_rec=False, cheap_proj=True)
                s_n = self.whnf_core(self.delta_reduction_core(*id_s), cheap_rec=False, cheap_proj=True)
        else:
            raise PanicError("Unreachable code reached in lazy_delta_reduction_step.")

        is_easy = self.def_eq_easy(t_n, s_n, expect_true=False)
        if is_easy is not None:
            return t_n, s_n, (ReductionStatus.EQUAL if is_easy else ReductionStatus.NOT_EQUAL)
        else: 
            return t_n, s_n, ReductionStatus.CONTINUE

    def lazy_delta_reduction(self, t_n : Expression, s_n : Expression, expect_true : bool) -> Tuple[Expression, Expression, Optional[bool]]:
        """
        Tries to compare the expressions t_n and s_n by unfolding the definitions of the functions of the applications. It loops until the expressions are equal, not equal, or definition unfolding will not help. 

        Args:
            t_n : Expression
                The first expression to compare.
            s_n : Expression
                The second expression to compare.

        Returns:
            Tuple[Expression, Expression, Optional[bool]]
                The expressions after the reduction, and the result of the comparison 
        """
        while True:
            try_offset = self.def_eq_offset(t_n, s_n, expect_true=False)
            if try_offset is not None:
                if expect_true and not try_offset: 
                    raise DefinitionalEqualityError(t_n, s_n)
                return t_n, s_n, try_offset

            if not t_n.has_fvars and not s_n.has_fvars: 
                nat_t = self.reduce_nat_lit(t_n) 
                if nat_t is not None: 
                    return t_n, s_n, self.def_eq_core(nat_t, s_n, expect_true)
                nat_s = self.reduce_nat_lit(s_n)
                if nat_s is not None: 
                    return t_n, s_n, self.def_eq_core(t_n, nat_s, expect_true)
            
            native_t = self.reduce_native(t_n)
            if native_t is not None:
                return t_n, s_n, self.def_eq_core(native_t, s_n, expect_true)
            native_s = self.reduce_native(s_n)
            if native_s is not None:
                return t_n, s_n, self.def_eq_core(t_n, native_s, expect_true)

            t_n, s_n, status = self.lazy_delta_reduction_step(t_n, s_n)

            if status == ReductionStatus.CONTINUE: continue
            elif status == ReductionStatus.EQUAL: 
                return t_n, s_n, True
            elif status == ReductionStatus.NOT_EQUAL: 
                return t_n, s_n, False
            elif status == ReductionStatus.UNKNOWN: 
                return t_n, s_n, None
            else: raise PanicError("Unknown reduction status.")

    def lazy_delta_proj_reduction(self, t_n : Expression, s_n : Expression, idx : int, expect_true : bool) -> bool:
        """
        Tries to lazy delta reduce the projections of the expressions t_n and s_n as much as possible. If in the end they are applications of projections, then it tries to reduce the projections using reduce_proj_core and compares the results.
        """
        while True:
            t_n, s_n, status = self.lazy_delta_reduction_step(t_n, s_n)
            if status is ReductionStatus.CONTINUE: continue
            elif status is ReductionStatus.EQUAL: 
                return True
            else:
                t = self.reduce_proj_core(t_n, idx)
                if t is not None:
                    s = self.reduce_proj_core(s_n, idx)
                    if s is not None:
                        return self.def_eq_core(t, s, expect_true)
                return self.def_eq_core(t_n, s_n, expect_true)
    
    def reduce_nat_lit(self, e : Expression) -> Optional[Expression]:
        """
        If the expression is natural number (without free variables), then this function tries to get its value using Python's built-in functions: +, -, *, **, etc to speed up computations.
        """
        if e.has_fvars: 
            return None
        
        fn, args, _ = unfold_app(e)
        if not isinstance(fn, Const): 
            return None
        if len(args) == 1:
            if fn.cname == self.environment.Nat_succ_name:
                arg = self.whnf(args[0])
                if isinstance(arg, NatLit): 
                    return NatLit(arg.val + 1, source=e.source)
                if is_nat_zero_const(self.environment, arg): 
                    return NatLit(1, source=e.source)
                return None
            
        if len(args) == 2:
            arg1 = self.whnf(args[0])
            if not isinstance(arg1, NatLit): 
                return None
            arg2 = self.whnf(args[1])
            if not isinstance(arg2, NatLit): 
                return None
            
            name = fn.cname
            if len(fn.lvl_params) != 0:
                raise DeclarationError(f"Expected no level parameters, but got {len(fn.lvl_params)} when reducing natural numbers.")
            if name == self.environment.Nat_add_name: 
                return reduce_bin_nat_op(nat_add, arg1.val, arg2.val, source=e.source)
            elif name == self.environment.Nat_sub_name: 
                return reduce_bin_nat_op(nat_sub, arg1.val, arg2.val, source=e.source)
            elif name == self.environment.Nat_mul_name: 
                return reduce_bin_nat_op(nat_mul, arg1.val, arg2.val, source=e.source)
            elif name == self.environment.Nat_pow_name: 
                return reduce_bin_nat_op(nat_pow, arg1.val, arg2.val, source=e.source)
            elif name == self.environment.Nat_gcd_name: 
                return reduce_bin_nat_op(nat_gcd, arg1.val, arg2.val, source=e.source)
            elif name == self.environment.Nat_mod_name: 
                return reduce_bin_nat_op(nat_mod, arg1.val, arg2.val, source=e.source)
            elif name == self.environment.Nat_div_name: 
                return reduce_bin_nat_op(nat_div, arg1.val, arg2.val, source=e.source)
            elif name == self.environment.Nat_eq_name: 
                return reduce_bin_nat_pred(self.environment, nat_beq, arg1.val, arg2.val, source=e.source)
            elif name == self.environment.Nat_le_name: 
                return reduce_bin_nat_pred(self.environment, nat_ble, arg1.val, arg2.val, source=e.source)
            elif name == self.environment.Nat_land_name: 
                return reduce_bin_nat_op(nat_land, arg1.val, arg2.val, source=e.source)
            elif name == self.environment.Nat_lor_name: 
                return reduce_bin_nat_op(nat_lor, arg1.val, arg2.val, source=e.source)
            elif name == self.environment.Nat_lxor_name: 
                return reduce_bin_nat_op(nat_xor, arg1.val, arg2.val, source=e.source)
            elif name == self.environment.Nat_shiftl_name: 
                return reduce_bin_nat_op(nat_shiftl, arg1.val, arg2.val, source=e.source)
            elif name == self.environment.Nat_shiftr_name: 
                return reduce_bin_nat_op(nat_shiftr, arg1.val, arg2.val, source=e.source)
        return None
    
    def quot_reduce_rec(self, e : Expression) -> Optional[Expression]:
        """
        Built in reduction for quotient recursor.
        """
        fn, args, arg_sources = unfold_app(e)
        if not isinstance(fn, Const): 
            return None
        mk_pos = 0 # the position of the Quot r argument
        arg_pos = 0 # the position of the element
        if fn.cname == self.environment.Quot_lift_name:
            mk_pos = 5
            arg_pos = 3
        elif fn.cname == self.environment.Quot_ind_name:
            mk_pos = 4
            arg_pos = 3
        else: 
            return None

        if len(args) <= mk_pos: return None
        mk = self.whnf(args[mk_pos]) # whnf to expose the Quot_mk

        mk_fn, mk_args, _ = unfold_app(mk)

        if not isinstance(mk_fn, Const): 
            return None
        if mk_fn.cname != self.environment.Quot_mk_name: 
            return None
        if len(mk_args) != 3: 
            return None # the Quot.mk takes 3 arguments

        if not isinstance(mk, App):
            raise PanicError("Wrong unfold_app result.")
        f = args[arg_pos] # get the function we are lifting/inducing
        r = App(f, mk.arg, source=arg_sources[mk_pos]) # get the class representative and apply f on it # TODO: check this again

        elim_arity = mk_pos+1
        if len(args) > elim_arity:
            r = fold_apps(r, args[elim_arity:], sources=arg_sources[elim_arity:]) # reapply the arguments that were not relevant for the recursor
        return r
    
    def inductive_reduce_rec(self, e : Expression, cheap_rec : bool, cheap_proj : bool) -> Optional[Expression]: # BIG TODO: return to this
        """
        Reduce the recursor application for inductive types.
        """
        # Second unfold the application and get the recursor
        rec_fn, rec_args, rec_arg_sources = unfold_app(e)
        if not isinstance(rec_fn, Const): 
            return None
        
        rec_decl = self.environment.get_declaration_under_name(rec_fn.cname, source=rec_fn.source)
        if not isinstance(rec_decl, Recursor): 
            return None

        major_index = rec_decl.get_major_index() # the position of the major premise

        if major_index >= len(rec_args): 
            return None
        major = rec_args[major_index] # the arguments of the major premise

        # if K-axiom is enabled, then we try to convert the major premise to the (only) constructor, see to_constructor_when_K
        if rec_decl.isK:
            major = self.to_constructor_when_K(rec_decl, major, cheap_rec=cheap_rec, cheap_proj=cheap_proj)

        # if the major premise is a literal, then we convert it to the corresponding constructor
        # if it is a structure, then we convert it to the (only) constructor, see to_constructor_when_structure
        major = self.whnf_core(major, cheap_rec=cheap_rec, cheap_proj=cheap_proj) if cheap_rec else self.whnf(major) 
        if isinstance(major, NatLit):
            major = nat_lit_to_constructor(self.environment, major)
        elif isinstance(major, StrLit):
            major = str_lit_to_constructor(self.environment, major)
        else:
            major = self.to_constructor_when_structure(rec_decl.get_major_induct(), major, inductive_name_source=rec_fn.source, cheap_rec=cheap_rec, cheap_proj=cheap_proj)
        
        prule = rec_decl.get_recursion_rule(major)
        if prule is None: 
            return None
        rule, _source_fn = prule

        _, major_args, major_arg_sources = unfold_app(major)
        if len(major_args) < rule.num_fields: 
            return None 
        if len(rec_fn.lvl_params) != len(rec_decl.lvl_params): 
            return None
        rhs = self.subst_level_params(rule.value, rec_decl.lvl_params, rec_fn.lvl_params, source=None) # clones the rule.value

        # apply parameters, motives and minor premises from recursor application.
        if rec_decl.num_params + rec_decl.num_motives + rec_decl.num_minors >= len(rec_args):
            RecursionError("Recursor application does not have enough arguments.")
        rhs = fold_apps(rhs, rec_args[:rec_decl.num_params + rec_decl.num_motives + rec_decl.num_minors], rec_arg_sources[:rec_decl.num_params + rec_decl.num_motives + rec_decl.num_minors]) # this is the actual reduction of the recursor

        # TODO: The number of parameters in the constructor is not necessarily
        #equal to the number of parameters in the recursor when we have
        #nested inductive types. 
        nparams = len(major_args) - rule.num_fields
        # apply fields from major premise
        if nparams + rule.num_fields > len(major_args):
            raise RecursionError(f"Major premise does not have the expected number of fields. Expected at least {nparams + rule.num_fields}, but got {len(major_args)}.")
        selected_major_args = major_args[nparams: nparams + rule.num_fields]
        selected_major_arg_sources = major_arg_sources[nparams: nparams + rule.num_fields]
        if len(selected_major_args) != rule.num_fields: raise RecursorError("Major premise does not have the expected number of fields.", source=e.source)
        rhs = fold_apps(rhs, selected_major_args, selected_major_arg_sources) # reapply the indices' arguments back

        # the remaining arguments are not relevant for the recursor; they are just applied back to whatever we got from the reduction
        if len(rec_args) > major_index + 1: 
            rhs = fold_apps(rhs, rec_args[major_index + 1:], rec_arg_sources[major_index + 1:])
        
        return rhs
    
    def reduce_recursor(self, e : Expression, cheap_rec : bool, cheap_proj : bool) -> Optional[Expression]:
        """
        Tries to reduce the recursor application (either quotient or inductive).
        """
        # First check if it is a quotient recursor and can be reduced
        r = self.quot_reduce_rec(e)
        if r is not None:
            return r
        
        # Then check if it is an inductive recursor and can be reduced
        i = self.inductive_reduce_rec(e, cheap_rec, cheap_proj)
        if i is not None:
            return i
        
        return None

    def reduce_native(self, e : Expression) -> Optional[Expression]:
        """
        TODO
        """
        if not isinstance(e, App): 
            return None
        if not isinstance(e.arg, Const): 
            return None
        if e.fn == Const(cname=self.environment.Bool_reduce_name, lvl_params=[], source=None):
            raise NotImplementedError("TODO")
            #object * r = ir::run_boxed(env, options(), const_name(arg), 0, nullptr);
            #if (!lean_is_scalar(r)) {
            #    lean_dec_ref(r);
            #    throw kernel_exception(env, "type checker failure, unexpected result value for 'Lean.reduceBool'");
            #}
            #return lean_unbox(r) == 0 ? some_expr(mk_bool_false()) : some_expr(mk_bool_true());
        if e.fn == Const(cname=self.environment.Nat_reduce_name, lvl_params=[], source=None):
            raise NotImplementedError("TODO")
            #object * r = ir::run_boxed(env, options(), const_name(arg), 0, nullptr);
            #if (lean_is_scalar(r) || lean_is_mpz(r)) {
            #    return some_expr(mk_lit(literal(nat(r))));
            #} else {
            #    throw kernel_exception(env, "type checker failure, unexpected result value for 'Lean.reduceNat'");
            #}

    # WHNF
    def whnf_fvar(self, fvar : FVar, cheap_rec : bool, cheap_proj : bool) -> Expression:
        """
        Reduces the value of the free variable to weak head normal form.
        """
        fvar_val = self.get_value_of_fvar(fvar) 
        if fvar_val is None:
            return fvar
        else:
            return self.whnf_core(fvar_val, cheap_rec=cheap_rec, cheap_proj=cheap_proj) 

    def whnf_core(self, expr : Expression, cheap_rec : bool, cheap_proj : bool) -> Expression:
        """
        The main function that reduces the expression to weak head normal form:
        - expressions that are already in whnf (BVar, Sort, MVar, Pi, Lambda, NatLit, StrLit, Const) are returned as is
        - if it is a let fvar, then it reduces the value of the fvar
        - checks cache for the result of more complex expressions,
        - if it is a projection, then it tries to reduce it using reduce_proj,
        - if it is an application it splits cases:
            - if the function is a lambda, then it beta reduces the application,
            - if the function is actaully an application of a recursor, then it tries to reduce it using reduce_recursor,
            - otherwise, it tries to reduce the function and the arguments and then fold them back and whnf further,
            - if it is a let, then it instantiates the body with the value and whnfs further.
        
        Caches the results of the more complex expressions when cheap_rec and cheap_proj are False.
        """
        if isinstance(expr, BVar) or isinstance(expr, Sort) or isinstance(expr, MVar) or isinstance(expr, Pi) or isinstance(expr, Lambda) or isinstance(expr, NatLit) or isinstance(expr, StrLit) or isinstance(expr, Const): 
            return expr
        elif isinstance(expr, FVar):
            if not expr.is_let: 
                return expr # the fvar has no val that can be reduced to
        
        cached_whnfed_expr = self.whnf_core_cache.get(expr)
        if cached_whnfed_expr is not None: 
            return cached_whnfed_expr

        r = None
        if isinstance(expr, FVar):
            return self.whnf_fvar(expr, cheap_rec=cheap_rec, cheap_proj=cheap_proj)
        elif isinstance(expr, Proj):
            pos_red = self.reduce_proj(expr, cheap_rec=cheap_rec, cheap_proj=False) 
            if pos_red is None:
                r = expr
            else:
                r = self.whnf_core(pos_red, cheap_rec=cheap_rec, cheap_proj=cheap_proj)     
        elif isinstance(expr, App):
            raw_fn, raw_args, raw_arg_sources = unfold_app(expr)
            assert len(raw_args) == len(raw_arg_sources)
            
            fn = self.whnf_core(raw_fn, cheap_rec=cheap_rec, cheap_proj=cheap_proj)
            if isinstance(fn, Lambda):
                r = self.whnf_core(self.beta_reduction(fn, raw_args, raw_arg_sources), cheap_rec=cheap_rec, cheap_proj=cheap_proj)
            elif fn == raw_fn:
                r = self.reduce_recursor(expr, cheap_rec=cheap_rec, cheap_proj=cheap_proj)
                if r is not None: 
                    red = self.whnf_core(r, cheap_rec=cheap_rec, cheap_proj=cheap_proj)
                    return red
                else: 
                    return expr
            else:
                r = self.whnf_core(fold_apps(fn, raw_args, raw_arg_sources), cheap_rec=cheap_rec, cheap_proj=cheap_proj)
        elif isinstance(expr, Let):
            r = self.whnf_core(self.instantiate(body=expr.body, val=expr.val), cheap_rec=cheap_rec, cheap_proj=cheap_proj)
        
        if r is None:
            raise PanicError(f"Expr of type {expr.__class__.__name__} could not be matched, this should not happen.")

        if (not cheap_rec) and (not cheap_proj): 
            if not expr.has_mvars: # cache the result if it does not have mvars
                self.whnf_core_cache.put(expr, r)

        return r
    
    def whnf(self, e : Expression) -> Expression:
        """
        More powerful version of whnf_core that aggressively unfolds definitions.
        """
        if isinstance(e, BVar) or isinstance(e, Sort) or isinstance(e, MVar) or isinstance(e, Pi) or isinstance(e, NatLit) or isinstance(e, StrLit): return e # easy, non-reducible cases
        elif isinstance(e, FVar):
            if not e.is_let: 
                return e

        # we don't check cache results for trivial cases
        cached_whnfed_expr = self.whnf_cache.get(e)
        if cached_whnfed_expr is not None: return cached_whnfed_expr

        # harder cases
        t = e
        while True:
            # first try to get whnf without unfolding definitions
            t1 = self.whnf_core(t, cheap_rec=False, cheap_proj=False)

            # if the expression is an application of a signal from lean to use Python's built in functions for faster computation for bools and nats
            v = self.reduce_native(t1)
            if v is not None:
                # cache the result of native reduction
                if not e.has_mvars: # cache the result if it does not have mvars
                    assert not v.has_mvars
                    self.whnf_cache.put(e, v)
                return v

            # if the expressions is nat it tries to reduce it using Python's built-in functions
            v = self.reduce_nat_lit(t1)
            if v is not None: 
                # cache the result of nat_lit reduction
                if not e.has_mvars: # cache the result if it does not have mvars
                    assert not v.has_mvars
                    self.whnf_cache.put(e, v)
                return v

            # Finally try to unfold definitions
            next_t = self.delta_reduction(t1)
            if next_t is not None:
                t = next_t
            else:
                r = t1
                # cache the result if it was NOT delta reduced
                if not e.has_mvars: # cache the result if it does not have mvars
                    assert not r.has_mvars
                    self.whnf_cache.put(e, r)
                return r

    # INFERENCE
    def infer_fvar(self, fvar : FVar):
        """
        Return the type belonging to the free variable.
        """
        return self.get_type_of_fvar(fvar)
    
    def infer_app(self, app : App, infer_only : bool) -> Expression:
        # BIG TODO: return to this
        """
        Infers the type of the application. Splits two cases not infer_only and infer_only. If infer_only is False, then it checks that the type of the function is a pi type and that the argument matches the domain of the function. If infer_only is True, then it only checks that the type of the function is a pi type and keeps substituting the arguments into the function type's codomain as deep as possible.
        """
        if not infer_only:
            # the function should be a pi type
            fn_type = self.ensure_pi(self.infer_core(app.fn, infer_only=(self.allow_unstrict_infer and infer_only)), pi_source=app)
            
            # get the type of the argument
            inferred_domain = self.infer_core(app.arg, infer_only=(self.allow_unstrict_infer and infer_only))

            # the domain of the function should be equal to the type of the argument
            if not self.def_eq(inferred_domain, fn_type.domain, expect_true=False):
                raise ExpectedEqualExpressionsError(inferred_domain, fn_type.domain, source=app.source)
            
            infered_type = self.instantiate(body=fn_type.codomain, val=app.arg)
            return infered_type
        else:
            # If infer_only is true we only check that the type of fn is a pi type and keep substituting the arguments into the function type's codomain. We don't check that arguments match the function type's domain.
            fn, args, arg_sources = unfold_app(app)
            fn_type = self.infer_core(fn, infer_only=(self.allow_unstrict_infer and infer_only))
            
            j = 0
            for i in range(len(args)):
                if isinstance(fn_type, Pi):
                    fn_type = fn_type.codomain
                else:
                    fn_type = self.instantiate_multiple(fn_type, args[j:i][::-1])

                    fn_type = self.ensure_pi(fn_type, pi_source=arg_sources[j].source)
                    fn_type = fn_type.codomain
                    
                    for k in range(j, i): # TODO: check if this is correct
                        if arg_sources[k].source.is_external:
                            self.fun_on_successful_inference(arg_sources[k].source, MVar()) # TODO: this is a hack

                    j = i

            ret = self.instantiate_multiple(fn_type, args[j:][::-1])

            for k in range(j, len(args)):
                if arg_sources[k].source.is_external:
                    self.fun_on_successful_inference(arg_sources[k].source, MVar())

            return ret
            
    def infer_sort(self, sort : Sort) -> Expression:
        """
        The type of Sort l is Sort (l+1).
        """
        return Sort(LevelSucc(sort.level))
    
    def infer_pi(self, pi : Pi, infer_only : bool) -> Expression:
        """
        Infers the type of the pi type. If pi is of the form (a_1 : A_1) ->( a_2 : A_2) -> ... -> (a_n : A_n) -> B, then the type of the pi is a sort with level
            imax lvl(type(A_1)) (imax lvl(type(A_2)) (... imax lvl(type(A_n)) lvl(type(B)) ...))
        
        where imax is the impredicative maximum, defined as:

        imax l m = \\begin{cases} 0 & \\text{if } m = 0 \\\\ max l m & \\text{if } m \\neq 0 \\end{cases}.

        The intuition for this definition is that if B is a proposition then the whole pi is a proposition.
        """
        fvars : List[FVar] = []
        us : List[Level] = []
        e = pi
        pi_sources : List[Expression] = []
        while isinstance(e, Pi):
            pi_sources.append(e)
            inst_domain = self.instantiate_multiple(e.domain, fvars[::-1])
            t1 = self.ensure_sort(self.infer_core(inst_domain, infer_only), sort_source=e.source)
            us.append(t1.level)
            fvars.append(self.create_fvar(e.bname, inst_domain, val=None, is_let=False, source=None))
            e = e.codomain

        e = self.instantiate_multiple(e, fvars[::-1])
        t1 = self.ensure_sort(self.infer_core(e, infer_only), sort_source=e.source)
        lvl = t1.level
        for i in range(len(us)-1, -1, -1):
            lvl = make_imax(us[i], lvl, source=None)

        self.cleanup_fvars(fvars)
        
        for pi_source in pi_sources:
            if pi_source.source.is_external:
                self.fun_on_successful_inference(pi_source.source, MVar())

        return Sort(level=lvl)
    
    def infer_const(self, c : Const) -> Expression:
        """
        The type of a constant is the type of the declaration of the constant.
        """
        decl = self.environment.get_declaration_under_name(c.cname, source=c.source)
        if len(c.lvl_params) != len(decl.lvl_params):
            raise PanicError("The number of level parameters of the constant does not match the number of level parameters in the environment.")
        return self.get_declaration_type_with_substituted_level_params(decl, c.lvl_params, source=None)

    def make_pi_binding(self, fvars : List[FVar], b : Expression, pi_sources : List[Optional[Any]]) -> Expression:
        """
        If we have a body with free variables fvars, then we abstract the body, replacing the free variables with bound variables, and then create Pi bindings corresponding to the bound variables. Also abstracts the domains of the pi bindings.

        Args:
            fvars : List[FVar]
                The list of free variables to be abstracted.
            b : Expression
                The body of the pi binding to be abstracted.
        """

        r = abstract_multiple_bvars(fvars[::-1], b)
        for i in range(len(fvars)-1, -1, -1):
            c_fvar = fvars[i]
            if c_fvar.is_let:
                raise PanicError("Cannot have a let binding in a pi binding.")
            abs_type = abstract_multiple_bvars(fvars[:i][::-1], c_fvar.original_type)
            r = Pi(c_fvar.name, abs_type, r, source=pi_sources[i])
        
        return r

    def infer_lambda(self, lam : Lambda, infer_only : bool) -> Expression:
        """
        The type of a lambda is the pi type with the same domain and codomain the type of the body of the lambda. The function also tries to cheaply reduce the number of free variables in the body of the lambda.
        """
        fvars : List[FVar] = []
        e = lam

        lambda_sources : List[Expression] = []
        while isinstance(e, Lambda):
            lambda_sources.append(e.source)
            inst_domain = self.instantiate_multiple(e.domain, fvars[::-1])
            fvars.append(self.create_fvar(e.bname, inst_domain, None, False, source=None))
            if not infer_only:
                self.ensure_sort(self.infer_core(inst_domain, infer_only), sort_source=e.domain.source)
            e = e.body
        
        r = self.instantiate_multiple(e, fvars[::-1])
        if r.has_loose_bvars:
            raise UnboundVariableError("The body of the lambda has loose bound variables.", source=lam.source)
        r = self.infer_core(r, infer_only)
        r = self.cheap_beta_reduce(r)

        r = self.make_pi_binding(fvars, r, pi_sources=len(lambda_sources) * [None])

        self.cleanup_fvars(fvars)

        for lambda_source in lambda_sources:
            if lambda_source.source.is_external:
                self.fun_on_successful_inference(lambda_source.source, MVar())

        return r
    
    def infer_nat_lit(self, n : NatLit) -> Expression:
        """
        The type of a natural number literal is Nat.
        """
        return Const(self.environment.Nat_name, [])
    
    def infer_string_lit(self, s : StrLit) -> Expression:
        """
        The type of a string literal is String.
        """
        return Const(self.environment.String_name, [])

    def make_let_binding(self, fvars : List[FVar], b : Expression, let_sources : List[Optional[Any]]) -> Expression:
        """
        If we have a body with free variables fvars, then we abstract the body, replacing the free variables with bound variables, and then create Let bindings corresponding to the bound variables (if they are present in the abstracted body). Also abstracts the domains and values of the let bindings. 
        """
        r = abstract_multiple_bvars(fvars[::-1], b)
        for i in range(len(fvars)-1, -1, -1):
            c_fvar = fvars[i]
            if not c_fvar.is_let:
                raise PanicError("Cannot have a non-let binding in a let binding.")
            if c_fvar.val is None:
                raise PanicError("Cannot have a let binding without a value.")

            abs_type = abstract_multiple_bvars(fvars[:i][::-1], c_fvar.original_type,) # TODO: think about this deeply

            ov = c_fvar.original_val
            assert ov is not None
            abs_val = abstract_multiple_bvars(fvars[:i][::-1], ov)

            r = Let(bname=c_fvar.name, domain=abs_type, val=abs_val, body=r, source=let_sources[i])
        
        return r
    
    def infer_let(self, let : Let, infer_only : bool) -> Expression:
        """
        The type of a let binding is the type of the body of the let binding where the value of the let binding is substituted for the bound variable in the body. The function tries to do this as deep as possible. It tries to cheaply reduce the number of lets in the body of the inferred type.

        If infer_only is False, then it checks that the type of the value of the let binding is equal to the domain of the let binding, and that the domain is a sort. 
        """
        fvars : List[FVar] = []
        vals : List[Expression] = []
        let_sources : List[Expression] = []

        e = let
        while isinstance(e, Let):
            l_type = self.instantiate_multiple(e.domain, fvars[::-1])
            val = self.instantiate_multiple(e.val, fvars[::-1])
            fvars.append(self.create_fvar(e.bname, l_type, val=val, is_let=True, source=None))
            vals.append(val)
            let_sources.append(e.source)

            if not infer_only:
                self.ensure_sort(self.infer_core(l_type, infer_only), sort_source=e.domain.source)
                inferred_val_type = self.infer_core(val, infer_only)

                if not self.def_eq(inferred_val_type, l_type, expect_true=False):
                    raise ExpectedEqualExpressionsError(inferred_val_type, l_type, source=e.source)
            
            e = e.body
        
        r = self.instantiate_multiple(e, fvars[::-1])
        r = self.infer_core(r, infer_only)
        r = self.cheap_beta_reduce(r)
        used = [False] * len(fvars)

        mark_used(fvars, r, used)
        for i in range(len(fvars)-1, -1, -1):
            if used[i]: # if the i-th fvar is not used in the r (the body of the let binding) then we don't need to check which other fvars are used in the value of it
                # go through and mark all the fvars that are used in the value of the i-th let binding
                # since for i-th fvars i+1, ..., n-th fvars are not used, we don't need to check them
                mark_used(fvars[:i], vals[i], used)
        
        used_fvars : List[FVar] = []
        used_let_sources : List[Expression] = []
        for i in range(len(fvars)):
            if used[i]:
                used_fvars.append(fvars[i])
                used_let_sources.append(let_sources[i])
        
        assert len(used_fvars) == len(used_let_sources)
        r = self.make_let_binding(used_fvars, r, let_sources=len(used_let_sources) * [None])

        self.cleanup_fvars(fvars)

        for let_source in let_sources:
            if let_source.source.is_external:
                self.fun_on_successful_inference(let_source.source, MVar())

        return r

    def infer_proj(self, proj : Proj, infer_only : bool) -> Expression:
        """
        The type of the projections is the type of the i-th field of the constructor of the structure. First it get the structure name and the corresponding constructor. Then it instantiates the arguments into the constructor until the i-th field is reached. Finally it returns the type of the i-th field. If the projection is a proposition, then it checks that it remains a proposition during the instantiation process. 
        """
        struct_type = self.infer_core(proj.expr, infer_only=(self.allow_unstrict_infer and infer_only))
        struct_type = self.whnf(struct_type)

        inductive_fn, args, _ = unfold_app(struct_type)
        if isinstance(inductive_fn, MVar):
            raise UnfinishedExpressionError(proj.source)
        
        if not isinstance(inductive_fn, Const):
            raise ProjectionError(f"Expected a constant when unfolding the struct type for projection but got {inductive_fn.__class__.__name__}", source=proj.source)
        if inductive_fn.cname != proj.sname:
            raise ProjectionError(f"Expected the struct name to be {proj.sname} but got {inductive_fn.cname}", source=proj.source)
        I_name = inductive_fn.cname

        I_decl = self.environment.get_declaration_under_name(I_name, source=inductive_fn.source)
        if not isinstance(I_decl, Inductive):
            raise ProjectionError(f"Expected an inductive type when unfolding the struct type for projection but got {I_decl.__class__.__name__}", source=proj.source)
        
        if I_decl.number_of_constructors != 1:
            raise ProjectionError(f"Expected the inductive type {I_name} to have exactly one constructor but got {I_decl.number_of_constructors}", source=proj.source)
        
        if len(args) != I_decl.num_params + I_decl.num_indices:
            raise ProjectionError(f"Expected the {I_decl.num_params + I_decl.num_indices} arguments but got {len(args)}, when unfolding the struct type for projection.", source=proj.source)

        constructor_decl = self.environment.get_declaration_under_name(I_decl.constructor_names[0], source=inductive_fn.source)

        if not isinstance(constructor_decl, Constructor):
            raise DeclarationError(f"Expected a constructor declaration for the first constructor of the inductive type {I_name} but got {constructor_decl.__class__.__name__}")

        if constructor_decl.num_params != I_decl.num_params:
            raise DeclarationError(f"Sanity check failed: number of parameters in inductive type and constructor do not match.")

        r = self.subst_level_params(constructor_decl.type, I_decl.lvl_params, inductive_fn.lvl_params, source=None)
        
        for i in range(I_decl.num_params):
            if i >= len(args):
                raise ProjectionError(f"Ran out of arguments when instantiating projection args.", source=proj.source)
            r = self.whnf(r)
            if isinstance(r, MVar):
                raise UnfinishedExpressionError(proj.source)
            if not isinstance(r, Pi):
                raise ProjectionError(f"Expected a Pi type when instantiating projection args but got {r.__class__.__name__}", source=proj.source)
            r = self.instantiate(body=r.codomain, val=args[i])
        
        is_prop_type = self.is_prop(r)

        for i in range(proj.index):
            r = self.whnf(r)
            if not isinstance(r, Pi):
                raise ProjectionError(f"Expected a Pi type when reducing projection indices but got {r.__class__.__name__}", source=proj.source)
            
            if r.codomain.has_loose_bvars:
                r = self.instantiate(body=r.codomain, val=Proj(I_name, i, proj.expr))
                if is_prop_type and not self.is_prop(r):
                    raise ProjectionError(f"When substituting proj indices, the body should remain a prop type.", source=proj.source)
            else:
                r = r.codomain
        
        r = self.whnf(r)
        if not isinstance(r, Pi):
            raise ProjectionError(f"Expected a Pi type for projection index but got {r.__class__.__name__}", source=proj.source)

        r = r.domain

        if is_prop_type and not self.is_prop(r):
            raise ProjectionError(f"The prop should remain a prop type after reducing the projection index.", source=proj.source)

        return r

    def infer_core(self, expr : Expression, infer_only : bool) -> Expression:
        """
        The main type checking function: infers the type of an expression. If inference fails it raises an error. It also caches the results of the inference.
        Note that infer_core (infer_core expr) results in a Sort expression.

        Args:
            expr : Expression : The expression to infer the type of.
            infer_only : bool : If we know an expression is well-typed, we can use the `infer_only` flag to skip some parts of the inference for performance reasons when we know that the expresssion is well-typed. 
        
        Returns:
            Expression : The inferred type of the expression.
        
        Raises: See KernelExceptions.py
        """
        if expr.has_loose_bvars:
            raise UnboundVariableError("Cannot infer the type of an expression with unbound variables.", source=expr.source)

        # check if expression is already in infer_cache (separate cache for infer_only)
        cached_inferred_type = self.infer_cache[infer_only].get(expr)
        if cached_inferred_type is not None: 
            return cached_inferred_type

        if isinstance(expr, BVar): 
            raise PanicError("Unreachable code reached: BVar in infer_core.")
        elif isinstance(expr, FVar): 
            inferred_type = self.infer_fvar(expr)
        elif isinstance(expr, MVar): 
            #return MVar() TODO: rerun tests
            raise UnfinishedExpressionError(expr.source)
        elif isinstance(expr, App): 
            inferred_type = self.infer_app(expr, infer_only=(self.allow_unstrict_infer and infer_only))
        elif isinstance(expr, Sort): 
            inferred_type = self.infer_sort(expr)
        elif isinstance(expr, Const): 
            inferred_type = self.infer_const(expr) 
        elif isinstance(expr, Lambda): 
            inferred_type = self.infer_lambda(expr, infer_only=(self.allow_unstrict_infer and infer_only))
        elif isinstance(expr, Pi): 
            inferred_type = self.infer_pi(expr, infer_only=(self.allow_unstrict_infer and infer_only))
        elif isinstance(expr, Let): 
            inferred_type = self.infer_let(expr, infer_only=(self.allow_unstrict_infer and infer_only))
        elif isinstance(expr, Proj): 
            inferred_type = self.infer_proj(expr, infer_only=(self.allow_unstrict_infer and infer_only))
        elif isinstance(expr, NatLit): 
            inferred_type = self.infer_nat_lit(expr)
        elif isinstance(expr, StrLit): 
            inferred_type = self.infer_string_lit(expr)
        else: 
            raise PanicError(f"Unknown expression type {expr.__class__.__name__}")

        if expr.source.is_external:
            self.fun_on_successful_inference(expr.source, inferred_type)
        
        # cache the result
        if not expr.has_mvars: # cache the result if it does not have mvars
            assert not inferred_type.has_mvars, f"{expr} was inferred to have mvars {inferred_type}"
            self.infer_cache[infer_only].put(expr, inferred_type)

        return inferred_type
    
    def clear_caches(self):
        """
        Clears all the caches in the type checker. Recommended to call this after each call to infer.
        """
        self.whnf_cache.clear()
        self.whnf_core_cache.clear()
        self.infer_cache[False].clear()
        self.infer_cache[True].clear()
        self.equiv_manager.clear()
        self.instantiation_cache.clear()
        self.instantiation_multiple_cache.clear()
        self.failure_cache.clear()
        self.lvl_param_subst_cache.clear()

    def infer(self, expr : Expression, clear_caches : bool = True, clear_local_context : bool = False) -> Expression:
        """
        A wrapper around infer_core that checks if the local context is empty before inferring the type of the expression. It also clears the caches if clear_caches is True.
        """

        if clear_local_context:
            self.local_context.clear()

        if not self.local_context.is_empty():
            raise PanicError(f"Local context is not empty when inferring: {self.local_context}")
        
        if clear_caches:
            self.clear_caches()

        inferred_type = self.infer_core(expr, infer_only=(self.allow_unstrict_infer and False))
        return inferred_type
    
    # DECLARATION CHECKING
    def check_declaration_info(self, decl : Declaration):
        """
        Checks the declaration info of a declaration:
        - the level parameters must be unique
        - the type must not contain free variables
        - the type must be well-formed
        - the inferred sort of the type must be a sort
        """
        if not are_unique_level_params(decl.lvl_params):
            raise DeclarationError(f"Level parameters {[str(l) for l in decl.lvl_params]} in declaration {decl.name} are not unique.")
        if decl.type.has_fvars:
            raise DeclarationError(f"Type of declaration {decl.name} contains free variables.")

        inferred_sort = self.infer(decl.type)
        self.ensure_sort(inferred_sort, sort_source=decl.type.source)

    def check_value_has_expected_type(self, value : Expression, expected_type : Expression, clear_caches : bool = True, clear_local_context : bool = False) -> bool:
        inferred_type = self.infer(value, clear_caches, clear_local_context)
        print(f"inferred_type {inferred_type}")
        return self.def_eq(inferred_type, expected_type, expect_true=True)
        
    def check_declaration_value(self, decl : Declaration):
        """
        Checks that the declaration value is well-typed and it is definitionally equal to the expected type provided by the declaration info.
        """
        if not (isinstance(decl, Definition) or isinstance(decl, Theorem) or isinstance(decl, Opaque)):
            raise DeclarationError(f"Declaration {decl.name} is not a Definition, Theorem, or Opaque, when checking declaration value. It is a {decl.__class__.__name__}.")

        if not self.check_value_has_expected_type(decl.value, decl.info.type):
            raise DeclarationError(f"Declaration {decl.name} ({decl.__class__.__name__}) has type different from the expected type. ") 

    def check_definition(self, d : Definition):
        """
        Checks the definition by checking its declaration info and value.
        """
        self.check_declaration_info(d)
        self.check_declaration_value(d)

    def check_theorem(self, t : Theorem):
        """
        Checks the theorem by checking its declaration info and value.
        """
        self.check_declaration_info(t)
        self.check_declaration_value(t)

    def check_opaque(self, o : Opaque):
        """
        Checks the opaque declaration by checking its declaration info and value.
        """
        self.check_declaration_info(o)
        self.check_declaration_value(o)

    def check_axiom(self, a : Axiom):
        """
        Checks the axiom by checking its declaration info. Axioms do not have values.
        """
        self.check_declaration_info(a)
    
    def check_inductive(self, ind : Inductive):
        """
        Checks the inductive type. This is the only instance in the Lean 4 where the dependencies form a cycle. See check_inductive_declaration_infos for more information.
        """
        self.check_inductive_declaration_infos(ind.name)

    def check_constructor(self, constructor : Constructor):
        """
        Checks the constructor by checking. Since it is one of the dependencies of the inductive type, it is checked using check_inductive_declaration_infos.
        """
        self.check_inductive_declaration_infos(constructor.inductive_name)

    def number_of_added_constructors(self, inductive_decl : Inductive) -> int:
        """
        Get the number of constructors present in the environment that are associated with the inductive type.
        """
        count = 0
        for constructor_name in inductive_decl.constructor_names:
            if self.environment.exists_declaration_under_name(constructor_name):
                constructor_decl = self.environment.get_declaration_under_name_no_source(constructor_name)
                if not isinstance(constructor_decl, Constructor): raise DeclarationError(f"Inductive type's constructor name {inductive_decl.name} refers to a non-constructor {constructor_name}.")
                count += 1
        return count
    
    def check_quotient(self, q : Quot):
        """
        Checks the quotient by checking its declaration info. Quotients do not have values.
        """
        self.check_declaration_info(q)
    
    def check_inductive_declaration_infos(self, inductive : Name):
        """
        Inductive types are special in that they are defined cyclically: the constructors and the inductive type refer to each other cyclically. Thus we cannot check them as they are added to the environment. Instead, we check them once each part of the inductive definition has been added to the environment. We mark the inductive type and its constructors as checked once they have been successfully checked.
        """
        # First check that all the constructors have been added
        if not self.environment.exists_declaration_under_name(inductive): return
        inductive_decl = self.environment.get_declaration_under_name_no_source(inductive)
        if not isinstance(inductive_decl, Inductive):
            raise DeclarationError(f"Inductive type {inductive} not found.")
        
        found_constructors = self.number_of_added_constructors(inductive_decl)
        if found_constructors < inductive_decl.number_of_constructors: return
        if found_constructors != inductive_decl.number_of_constructors:
            raise DeclarationError(f"Sanity check failed: number of found constructors does not match the number of expected constructors.")

        self.environment.checking_inductive = True
        # After all the constructors have been added, we can check the inductive type and its constructors
        self.check_declaration_info(inductive_decl)

        # Now check that the inductive type
        for i, constructor_name in enumerate(inductive_decl.constructor_names):
            constructor_decl = self.environment.get_declaration_under_name_no_source(constructor_name)
            self.check_declaration_info(constructor_decl)
            if not isinstance(constructor_decl, Constructor):
                raise DeclarationError(f"Sanity check failed: constructor {constructor_name} is not a constructor.")

            if i != constructor_decl.c_index:
                raise DeclarationError(f"Constructor {constructor_name} has index {constructor_decl.c_index} but should have index {i}.")

            if inductive_decl.num_params != constructor_decl.num_params:
                raise DeclarationError(f"Constructor {constructor_name} has {constructor_decl.num_params} parameters but the inductive type {constructor_decl.inductive_name} has {inductive_decl.num_params} parameters.")

        inductive_decl.is_checked = True
        for constructor_name in inductive_decl.constructor_names:
            constructor_decl = self.environment.get_declaration_under_name_no_source(constructor_name)
            self.check_declaration_info(constructor_decl)
            if not isinstance(constructor_decl, Constructor):
                raise PanicError(f"Unreachable code reached: constructor {constructor_name} is not a constructor.")
            constructor_decl.is_checked = True # CHANGES INDUCTIVE, BUT THIS IS OK
        self.environment.checking_inductive = False # CHANGES INDUCTIVE, BUT THIS IS OK

    def check_recursor(self, recursor : Recursor):
        """
        Checks the recursor by checking its declaration info and the recursor rules. The recursor rules are only checked for the presence of the associated constructors; their types are not checked.
        """
        self.check_declaration_info(recursor)

        for rec_rule in recursor.recursor_rules:
            constructor_decl = self.environment.get_declaration_under_name_no_source(rec_rule.constructor)
            if not isinstance(constructor_decl, Constructor):
                raise DeclarationError(f"Recursor rule for {rec_rule.constructor} is not associated with a constructor; found {constructor_decl.__class__.__name__} with name {constructor_decl.info.ciname} instead.")

    def check_declaration(self, decl : Declaration):
        """
        The main function that checks the declaration. It splits the cases based on the type of the declaration and calls the appropriate check function.
        """
        print(f"Checking declaration {decl.name}")
        if isinstance(decl, Definition): self.check_definition(decl)
        elif isinstance(decl, Theorem): self.check_theorem(decl)
        elif isinstance(decl, Opaque): self.check_opaque(decl)
        elif isinstance(decl, Axiom): self.check_axiom(decl)
        elif isinstance(decl, Inductive): self.check_inductive(decl)
        elif isinstance(decl, Constructor): self.check_constructor(decl)
        elif isinstance(decl, Recursor): self.check_recursor(decl)
        elif isinstance(decl, Quot): self.check_quotient(decl)
        else: raise DeclarationError(f"Unknown declaration type {decl.__class__.__name__}")