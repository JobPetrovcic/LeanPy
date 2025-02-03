import sys
from typing import List, Optional, Sequence, Tuple
from LeanPy.Kernel.Cache.Cache import InferCache, PairCache, WHNFCache # TODO: Pair cache is redundant, can be replace by map from tuple to value
from LeanPy.Kernel.Cache.EquivManager import EquivManager, FailureCache
from LeanPy.Kernel.KernelErrors import *
from LeanPy.Structures.Environment.Declarations.Declaration import Declaration, compare_reducibility_hints
from LeanPy.Structures.Environment.Environment import Environment
from LeanPy.Structures.Environment.LocalContext import LocalContext
from LeanPy.Structures.Environment.NatReduction import *
from LeanPy.Structures.Environment.ReducibilityHint import Regular
from LeanPy.Structures.Expression.ExpressionManipulation import *
from LeanPy.Structures.Expression.LevelManipulation import *
from LeanPy.Structures.Name import Name
from LeanPy.Structures.Expression.Level import *
from LeanPy.Structures.Expression.Expression import *
from LeanPy.Structures.Environment.Declarations.Declaration import *


class TypeChecker:
    def __init__(
            self, 
            allow_unstrict_infer : bool = False, # TODO: change this after testing
            environment : Environment | None = None
        ):
        self.allow_unstrict_infer = allow_unstrict_infer

        self.whnf_cache = WHNFCache()
        self.whnf_core_cache = WHNFCache()
        self.infer_cache = [InferCache(), InferCache()]
        self.equiv_manager = EquivManager()
        self.failure_cache = FailureCache()
        self.instantiation_cache = PairCache[Expression, Expression, Expression]()
        self.instantiation_multiple_cache = PairCache[Expression, Tuple[Expression, ...], Expression]()
        self.lvl_param_subst_cache = PairCache[Expression, Tuple[Tuple[LevelParam, Level], ...], Expression]()

        if environment is None:
            self.environment = Environment()
        else:
            self.environment = environment
        
        self.local_context = LocalContext()

    def remove_fvar(self, fvar: FVar):
        self.local_context.remove_fvar(fvar)

    def create_fvar(self, name: Name, type: Expression, val : Optional[Expression], is_let : bool) -> FVar:
        fvar = FVar(name, type, val, is_let=is_let)
        self.local_context.add_fvar(fvar)
        return fvar
    
    def get_type_of_fvar(self, fvar : FVar) -> Expression:
        return self.local_context.get_fvar_type(fvar)
    
    def get_value_of_fvar(self, fvar : FVar) -> Optional[Expression]:
        return self.local_context.get_fvar_value(fvar)
    
    def instantiate(self, body : Expression, val : Expression) -> Expression:
        """
        Replace the outermost bound variable in the body with the value. Clones the body(!).
        """
        cached_inst_body = self.instantiation_cache.get(body, val)
        if cached_inst_body is not None: 
            return cached_inst_body

        inst_body = instantiate_bvar(body, val)
        self.instantiation_cache.put(body, val, inst_body)
        return inst_body
    
    def instantiate_multiple(self, body : Expression, vals : Sequence[Expression]) -> Expression:
        """
        Replace the outermost bound variables in the body with the values. Clones the body(!).
        IMPORTANT: vals should be in order of the innermost bound variable to the outermost bound variable.
        """
        vals_tuple = tuple(vals)
        cached_inst_body = self.instantiation_multiple_cache.get(body, vals_tuple)
        if cached_inst_body is not None: 
            return cached_inst_body

        inst_body = instantiate_bvars(body, vals_tuple)
        self.instantiation_multiple_cache.put(body, vals_tuple, inst_body)
        return inst_body
    
    def subst_level_params(self, expr : Expression, lvl_params : List[LevelParam], levels : List[Level]) -> Expression:
        """
        Substitute the level parameters in the expression with the levels. Allows for caching.
        """
        lvl_subst = level_zip(lvl_params, levels)
        lvl_subst_tuple = tuple(lvl_subst)

        cached_subst_expr = self.lvl_param_subst_cache.get(expr, lvl_subst_tuple)
        if cached_subst_expr is not None: 
            return cached_subst_expr

        subst_expr = substitute_level_params_in_expression(expr, lvl_subst)
        self.lvl_param_subst_cache.put(expr, lvl_subst_tuple, subst_expr)

        return subst_expr
    
    def get_declaration_type_with_substituted_level_params(self, decl : Declaration, subs : List[Level]) -> Expression:
        if len(decl.lvl_params) != len(subs):
            raise DeclarationError(f"""
            Declaration {decl.name} has {len(decl.lvl_params)} level parameters, but {len(subs)} substitutions were provided.

            Decl parameters : {[str(l) for l in decl.lvl_params]}
            Subs parameters : {[str(l) for l in subs]}
            """)
        return self.subst_level_params(decl.type, decl.lvl_params, subs)
    
    def get_declaration_val_with_substituted_level_params(self, decl : Definition | Theorem | Opaque, subs : List[Level]) -> Expression:
        if len(decl.lvl_params) != len(subs):
            raise DeclarationError(f"""
            Declaration {decl.name} has {len(decl.lvl_params)} level parameters, but {len(subs)} substitutions were provided.

            Decl parameters : {[str(l) for l in decl.lvl_params]}
            Subs parameters : {[str(l) for l in subs]}
            """)
        return self.subst_level_params(decl.value, decl.lvl_params, subs)
        
    def instantiate_fvar(
            self, 
            bname : Name, 
            domain : Expression, # the type of the fvar
            arg_val : Optional[Expression],  # the value of the fvar
            body : Expression, # the body in which the fvar is instantiated
            is_let : bool = False
        ) -> Tuple[FVar, Expression]: # CHECKED
        fvar = self.create_fvar(bname, domain, arg_val, is_let=is_let)
        return fvar, self.instantiate(body, fvar)
    
    def abstract(self, fvar : FVar, expr : Expression) -> Expression: # CHECKED
        """Abstracts the outermost bound variable in the given expression."""
        # TODO: caching?
        self.remove_fvar(fvar)
        abstract_expression = abstract_bvar(expr, fvar)
        return abstract_expression
    
    def ensure_pi(self, expr : Expression) -> Pi: # CHECKED
        if isinstance(expr, Pi): 
            return expr
        
        whnfed_expr = self.whnf(expr)
        if  isinstance(whnfed_expr, Pi): 
            return whnfed_expr
        else: 
            raise ExpectedEqualExpressionsConstructorsError(Pi, whnfed_expr.__class__)
    
    def ensure_sort(self, e : Expression) -> Sort:
        if isinstance(e, Sort): 
            return e
        whnfd_e = self.whnf(e)
        if isinstance(whnfd_e, Sort): 
            return whnfd_e
        
        raise ExpectedEqualExpressionsConstructorsError(Sort, whnfd_e.__class__)
    
    
    def is_structure_like(self, decl_name : Name) -> bool:
        decl = self.environment.get_declaration_under_name(decl_name)
        if not isinstance(decl, Inductive): 
            return False
        return decl.number_of_constructors == 1 and decl.num_indices == 0 and not decl.is_recursive
    
    def is_prop(self, e : Expression, cheap_rec : bool = False, cheap_proj : bool = False) -> bool:
        if cheap_rec:
            inferred_type = self.whnf_core(self.infer_core(e, infer_only=(self.allow_unstrict_infer and True)), cheap_rec=cheap_rec, cheap_proj=cheap_proj)
        else:
            inferred_type = self.whnf(self.infer_core(e, infer_only=(self.allow_unstrict_infer and True)))
        return isinstance(inferred_type, Sort) and is_equivalent(inferred_type.level, self.environment.level_zero)
    
    # DEFINITIONAL EQUALITY
    def def_eq_sort(self, l : Sort, r : Sort) -> bool:
        """Sorts are equal if their levels satisfy antisymmetry.
        The comparsion function does not change anything, so def_eq_sort is safe to use when passing by reference.
        """
        return is_equivalent(l.level, r.level)
    
    def def_eq_const(self, l : Const, r : Const) -> bool:
        """
        If the names are the same, and the level parameters are equal, then the constants are equal.
        Since nothing is changed, this function is safe to use when passing by reference.
        """
        if l.cname == r.cname:
            if is_equivalent_list(l.lvl_params, r.lvl_params): 
                return True
            else: print(f"Constants {l} and {r} have the same name but different level parameters : {[str(lvl) for lvl in l.lvl_params]} and {[str(lvl) for lvl in r.lvl_params]}", file=sys.stderr)
        return False
    
    def def_eq_app(self, l : App, r : App) -> bool:
        f_fn, f_args = unfold_app(l.fn)
        g_fn, g_args = unfold_app(r.fn)
        if not self.def_eq(f_fn, g_fn):
            return False
        
        if len(f_args) != len(g_args): 
            return False
        for f_arg, g_arg in zip(f_args, g_args):
            if not self.def_eq(f_arg, g_arg):
                return False
        return True

    def def_eq_pi(self, init_t : Pi , init_s : Pi) -> bool:
        subs : List[FVar] = []
    
        t : Expression = init_t
        s : Expression = init_s
        while isinstance(t, Pi) and isinstance(s, Pi):
            var_s_type = None
            if t.domain != s.domain:
                var_s_type = self.instantiate_multiple(s.domain, subs[::-1])
                var_t_type = self.instantiate_multiple(t.domain, subs[::-1])
                if not self.def_eq(var_t_type, var_s_type):
                    return False
            if t.codomain.has_loose_bvars or s.codomain.has_loose_bvars:
                if var_s_type is None:
                    var_s_type = self.instantiate_multiple(s.domain, subs[::-1])
                subs.append(self.create_fvar(s.bname, var_s_type, None, is_let=False))
            else:
                subs.append(self.create_fvar(self.environment.filler_name, self.environment.filler_const, None, is_let=False))
            t = t.codomain
            s = s.codomain
        ret = self.def_eq(self.instantiate_multiple(t, subs[::-1]), self.instantiate_multiple(s, subs[::-1]))

        for sub in subs[::-1]:
            self.remove_fvar(sub)
        return ret
    
    def def_eq_lambda(self, init_it : Lambda , init_s : Lambda) -> bool:
        subs : List[FVar] = []
    
        t : Expression = init_it
        s : Expression = init_s
        while isinstance(t, Lambda) and isinstance(s, Lambda):
            var_s_type = None
            if not (t.domain == s.domain):
                var_s_type = self.instantiate_multiple(s.domain, tuple(subs[::-1]))
                var_t_type = self.instantiate_multiple(t.domain, tuple(subs[::-1]))
                if not self.def_eq(var_t_type, var_s_type):
                    return False
            if t.body.has_loose_bvars or s.body.has_loose_bvars:
                if var_s_type is None:
                    var_s_type = self.instantiate_multiple(s.domain, tuple(subs[::-1]))
                subs.append(self.create_fvar(s.bname, var_s_type, None, is_let=False))
            else:
                subs.append(self.create_fvar(self.environment.filler_name, self.environment.filler_const, None, is_let=False))
            t = t.body
            s = s.body
        ret = self.def_eq(self.instantiate_multiple(t, tuple(subs[::-1])), self.instantiate_multiple(s, tuple(subs[::-1])))
        for sub in subs[::-1]:
            self.remove_fvar(sub)
        return ret

    def are_struct_eq_exprs(self, a : Expression, b : Expression, use_hash : bool) -> bool:
        if a is b: 
            return True
        if use_hash and a.hash != b.hash: 
            return False
        if isinstance(a, BVar) and isinstance(b, BVar): 
            return a.db_index == b.db_index

        # check the equivalence manager
        dsu_ra = self.equiv_manager.expr_to_dsu_root(a)
        dsu_rb = self.equiv_manager.expr_to_dsu_root(b)
        if dsu_ra is dsu_rb: 
            return True
        
        # fall back to structural equality
        if a.__class__ != b.__class__: 
            return False

        result = False
        if isinstance(a, BVar) and isinstance(b, BVar): raise PanicError("Unreachable code reached: BVar should have been handled by the first if statement.")
        elif isinstance(a, Const) and isinstance(b, Const): result = self.def_eq_const(a, b)
        #elif isinstance(a, MVar) and isinstance(b, MVar): result = (a is b)
        elif isinstance(a, FVar) and isinstance(b, FVar): result = (a is b)
        elif isinstance(a, App) and isinstance(b, App): result = self.are_struct_eq_exprs(a.fn, b.fn, use_hash) and self.are_struct_eq_exprs(a.arg, b.arg, use_hash)
        elif isinstance(a, Lambda) and isinstance(b, Lambda): result = self.are_struct_eq_exprs(a.domain, b.domain, use_hash) and self.are_struct_eq_exprs(a.body, b.body, use_hash)
        elif isinstance(a, Pi) and isinstance(b, Pi): result = self.are_struct_eq_exprs(a.domain, b.domain, use_hash) and self.are_struct_eq_exprs(a.codomain, b.codomain, use_hash)
        elif isinstance(a, Sort) and isinstance(b, Sort): result = self.def_eq_sort(a, b)
        elif isinstance(a, NatLit) and isinstance(b, NatLit): result = (a.val == b.val)
        elif isinstance(a, StrLit) and isinstance(b, StrLit): result = (a.val == b.val)
        # what about MData?
        elif isinstance(a, Proj) and isinstance(b, Proj): result = a.index == b.index and self.are_struct_eq_exprs(a.expr, b.expr, use_hash)
        elif isinstance(a, Let) and isinstance(b, Let): result = self.are_struct_eq_exprs(a.domain, b.domain, use_hash) and self.are_struct_eq_exprs(a.val, b.val, use_hash) and self.are_struct_eq_exprs(a.body, b.body, use_hash)
        else: raise PanicError(f"Unreachable code reached: Cannot compare expressions {a} and {b} of class {a.__class__} and {b.__class__}.")
        
        if result:
            self.equiv_manager.add_equiv(dsu_ra, dsu_rb)

        return result

    def def_eq_easy(self, l: Expression, r: Expression, use_hash : bool = False) -> Optional[bool]:
        if self.are_struct_eq_exprs(l, r, use_hash): 
            return True

        if not (l.__class__ == r.__class__): 
            return None # not an easy case

        if isinstance(l, Sort) and isinstance(r, Sort): 
            return self.def_eq_sort(l, r)
        elif isinstance(l, BVar) or isinstance(r, BVar): raise PanicError("BVar should have been substituted by now, when comparing expressions for definitional equality.")
        
        elif isinstance(l, Pi) and isinstance(r, Pi):
            return self.def_eq_pi(l, r)
        elif isinstance(l, Lambda) and isinstance(r, Lambda):
            return self.def_eq_lambda(l, r)
        elif isinstance(l, NatLit) and isinstance(r, NatLit): 
            return l.val == r.val
        elif isinstance(l, StrLit) and isinstance(r, StrLit): 
            return l.val == r.val

    def def_eq_proof_irrel(self, t : Expression, s : Expression) -> Optional[bool]:
        """ Proof irrelevance support for propositions. If two expressions have equal types, and the types are proposition, then the expressions are considered equal. """
        t_type = self.infer_core(t, infer_only=(self.allow_unstrict_infer and True))
        if not self.is_prop(t_type):
            return None
        s_type = self.infer_core(s, infer_only=(self.allow_unstrict_infer and True))
        return self.def_eq(t_type, s_type)
    
    def def_eq_unit_like(self, t : Expression, s : Expression) -> bool:
        t_type = self.whnf(self.infer_core(t, infer_only=(self.allow_unstrict_infer and True)))
        inductive_const = get_app_function(t_type)

        if not isinstance(inductive_const, Const): 
            return False
        if not self.is_structure_like(inductive_const.cname): 
            return False

        constructor = self.get_first_constructor(inductive_const.cname)
        if constructor is None: 
            return False
        if constructor.num_fields != 0: 
            return False
        return self.def_eq_core(t_type, self.infer_core(s, infer_only=(self.allow_unstrict_infer and True)))
    
    def def_eq_core(self, l: Expression, r: Expression) -> bool:
        is_easy = self.def_eq_easy(l, r, use_hash=True)
        if is_easy is not None: 
            return is_easy

        if not l.has_fvars and isinstance(r, Const) and r.cname == self.environment.Bool_true_name:
            whnfd_l = self.whnf(l)
            if isinstance(whnfd_l, Const) and whnfd_l.cname == self.environment.Bool_true_name:
                return True

        l_n = self.whnf_core(l, cheap_rec=False, cheap_proj=True)
        r_n = self.whnf_core(r, cheap_rec=False, cheap_proj=True)
     
        if (l_n is not l) or (r_n is not r):
            is_easy = self.def_eq_easy(l_n, r_n)
            if is_easy is not None: 
                return is_easy

        is_proof_irr = self.def_eq_proof_irrel(l_n, r_n)
        if is_proof_irr is not None: 
            return is_proof_irr

        l_n_n, r_n_n, try_lazy = self.lazy_delta_reduction(l_n, r_n)
        if try_lazy is not None: 
            return try_lazy

        if isinstance(l_n_n, Const) and isinstance(r_n_n, Const):
            if self.def_eq_const(l_n_n, r_n_n): 
                return True
        if isinstance(l_n_n, FVar) and isinstance(r_n_n, FVar) and (l_n_n is r_n_n): 
            return True
        if isinstance(l_n_n, Proj) and isinstance(r_n_n, Proj) and l_n_n.index == r_n_n.index:
            if self.lazy_delta_proj_reduction(l_n_n.expr, r_n_n.expr, l_n_n.index): 
                return True

        l_n_n_n = self.whnf_core(l_n_n, cheap_rec=False, cheap_proj=False) # don't use cheap_proj now
        r_n_n_n = self.whnf_core(r_n_n, cheap_rec=False, cheap_proj=False) # don't use cheap_proj now

        if (l_n_n_n is not l_n_n) or (r_n_n_n is not r_n_n): 
            return self.def_eq_core(l_n_n_n, r_n_n_n)

        if isinstance(l_n_n_n, App) and isinstance(r_n_n_n, App):
            if self.def_eq_app(l_n_n_n, r_n_n_n): 
                return True

        # Try reductions
        if self.try_eta_expansion(l_n_n_n, r_n_n_n):
            return True
        if self.try_structural_eta_expansion(l_n_n_n, r_n_n_n):
            return True
        #
        ##r = try_string_lit_expansion(t_n, s_n); TODO
        ##if (r != l_undef) return r == l_true;

        if self.def_eq_unit_like(l_n_n_n, r_n_n_n): 
            return True

        return False
    
    def def_eq(self, l: Expression, r: Expression) -> bool:
        ret = self.def_eq_core(l, r)
        if ret: self.equiv_manager.add_equiv_expressions(l, r)
        return ret

    # EXPANSIONS
    def try_eta_expansion_core(self, t : Expression, s : Expression) -> bool:
        """
        Tries to eta expand s: if s is a function, then by eta expansion, it is equal to the expression "fun x => s x".
        """
        if not (isinstance(t, Lambda) and (not isinstance(s, Lambda))): 
            return False
        
        s_type = self.whnf(self.infer_core(s, infer_only=(self.allow_unstrict_infer and False)))
        if not isinstance(s_type, Pi): 
            return False
        new_s = Lambda(bname=s_type.bname, domain=s_type.domain, body=App(s, BVar(0)))
        return self.def_eq(t, new_s)
    
    def try_eta_expansion(self, t : Expression, s : Expression) -> bool:
        """
        Tries to eta expand y and compares it to x, then tries to eta expand x and compares it to y.
        """
        return self.try_eta_expansion_core(t, s) or self.try_eta_expansion_core(s, t)
    
    def try_structural_eta_expansion_core(self, t : Expression, s : Expression) -> bool: # CHECKED
        # First part: deconstruct s, ensure it is an application of a constructor
        s_fn, s_args = unfold_app(s)

        if not isinstance(s_fn, Const): 
            return False
        
        decl = self.environment.get_declaration_under_name(s_fn.cname)
        if not isinstance(decl, Constructor): 
            return False

        # Second part: ensure that the application has the correct number of arguments and that the inductive type is a structure
        if len(s_args) != decl.num_params + decl.num_fields: 
            return False
        if not self.is_structure_like(decl.inductive_name): 
            return False

        # Third part: ensure that the types are equal
        if not self.def_eq(
            self.infer_core(t, infer_only=(self.allow_unstrict_infer and True)),
            self.infer_core(s, infer_only=(self.allow_unstrict_infer and True)),
        ): 
            return False

        # Fourth part: ensure that the arguments are equal:
        # s was decomposed, so we know the arguments
        # for t we don't know the arguments, so we use proj to get them
        for i in range(decl.num_params, len(s_args)):
            t_i_proj = Proj(sname=decl.inductive_name, index=i-decl.num_params, expr=t)

            # compare the arguments
            if not self.def_eq(t_i_proj, s_args[i]): 
                return False
        return True
    
    def try_structural_eta_expansion(self, t : Expression, s : Expression) -> bool:
        return self.try_structural_eta_expansion_core(t, s) or self.try_structural_eta_expansion_core(s, t)
    

    # CONSTRUCTORS
    def get_constructor(self, constructor_name : Name) -> Constructor:
        decl = self.environment.get_declaration_under_name(constructor_name)
        if not isinstance(decl, Constructor):
            raise DeclarationError(f"Name {constructor_name} is not a constructor.")
        return decl
    
    def expand_eta_struct(self, e_type : Expression, e : Expression):
        fn, args = unfold_app(e_type)
        if not isinstance(fn, Const): 
            return e

        constructor = self.get_first_constructor(fn.cname)
        if not constructor: 
            return e

        if len(args) < constructor.num_params:
            raise StructureError(f"Expected {constructor.num_params} parameters, but got {len(args)}.")
        args = args[:constructor.num_params]
        result = fold_apps(Const(cname=constructor.name, lvl_params=fn.lvl_params), args)
        result = fold_apps(result, [Proj(sname=fn.cname, index=i, expr=e) for i in range(constructor.num_fields)])
        return result

    def to_constructor_when_structure(self, inductive_name : Name, e : Expression, cheap_rec : bool, cheap_proj : bool) -> Expression:
        if not self.is_structure_like(inductive_name): 
            return e

        f = get_app_function(e)
        if isinstance(f, Const) and isinstance(self.environment.get_declaration_under_name(f.cname), Constructor): 
            return e

        e_type = self.whnf_core(self.infer_core(e, infer_only=(self.allow_unstrict_infer and True)), cheap_rec=cheap_rec, cheap_proj=cheap_proj) if cheap_rec else self.whnf(self.infer_core(e, infer_only=(self.allow_unstrict_infer and True)))

        e_type_fn = get_app_function(e_type)
        if not (isinstance(e_type_fn, Const) and e_type_fn.cname == inductive_name): 
            return e 

        if self.is_prop(e_type, cheap_rec=cheap_rec, cheap_proj=cheap_proj): 
            return e
        return self.expand_eta_struct(e_type, e)

    def get_first_constructor(self, inductive_name : Name) -> Optional[Constructor]:
        decl = self.environment.get_declaration_under_name(inductive_name)
        if not isinstance(decl, Inductive): 
            return None
        if decl.number_of_constructors == 0: 
            return None
        return self.get_constructor(decl.constructor_names[0])
    
    def mk_nullary_constructor(self, type_e : Expression, num_params : int) -> Optional[Expression]:
        d, args = unfold_app(type_e)
        if not isinstance(d, Const): 
            return None
        constructor = self.get_first_constructor(d.cname)
        if constructor is None: 
            return None
        if len(args) < num_params:
            raise StructureError(f"Expected at least {num_params} parameters, but got {len(args)}.")
        args = args[:num_params]
        return fold_apps(Const(cname=constructor.name, lvl_params=d.lvl_params), args)

    def to_constructor_when_K(self, recursor : Recursor, e : Expression, cheap_rec : bool, cheap_proj : bool) -> Expression:
        """See https://stackoverflow.com/questions/39239363/what-is-axiom-k
        For datatypes that support K-axiom, given `e` an element of that type, we convert (if possible)
        to the default constructor. For example, if `e : a = a`, then this method returns `eq.refl a` """
        assert recursor.isK, "Cannot apply K-axiom to a recursor that is not K."
        app_type = self.infer_core(e, infer_only=(self.allow_unstrict_infer and True))
        app_type = self.whnf_core(app_type, cheap_rec=cheap_rec, cheap_proj=cheap_proj) if cheap_rec else self.whnf(app_type)
        app_type_inductive, app_type_args = unfold_app(app_type)

        if not isinstance(app_type_inductive, Const): 
            return e
        if app_type_inductive.cname != recursor.get_major_induct(): 
            return e # type incorrect

        # special handling of mvars
        # TODO: check if this is correct
        if app_type.has_expr_mvars:
            # if app_type has mvars, then we can apply K-axiom only if all the arguments are mvar-free
            for i in range(recursor.num_params, len(app_type_args)):
                if app_type_args[i].has_expr_mvars:
                    return e

        new_constructor_app = self.mk_nullary_constructor(app_type, recursor.num_params)
        if not new_constructor_app: 
            return e
        new_type = self.infer_core(new_constructor_app, infer_only=(self.allow_unstrict_infer and True))

        if not self.def_eq(app_type, new_type): 
            return e
        return new_constructor_app
    
    # REDUCTIONS

    def cheap_beta_reduce(self, e : Expression) -> Expression: # TODO: check again
        if not isinstance(e, App): 
            return e
        fn, args = unfold_app(e)
        if not isinstance(fn, Lambda):
            return e
        
        i = 0
        while isinstance(fn, Lambda) and i < len(args):
            i += 1
            fn = fn.body
        
        if not fn.has_loose_bvars:
            return fold_apps(fn, args[i:])
        elif isinstance(fn, BVar):
            if i <= fn.db_index:
                raise PanicError(f"Unreachable code reached: i = {i} <= fn.db_index = {fn.db_index}.")
            return fold_apps(args[i - fn.db_index - 1], args[i:])
        else:
            return e

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
    
    def is_delta(self, expr : Expression) -> Optional[Tuple[Const, Definition | Opaque | Theorem, List[Expression]]]:
        """Checks if the expression is delta reducible: if it is an application of a declaration, then it returns the declaration and the arguments. Otherwise, it returns None."""
        fn, args = unfold_app(expr)
        if not isinstance(fn, Const): 
            return None
        decl = self.environment.get_declaration_under_name(fn.cname)
        if not decl.has_value(): 
            return None
        assert isinstance(decl, Definition) or isinstance(decl, Opaque) or isinstance(decl, Theorem)
        return fn, decl, args
    
    def delta_reduction_core(self, fn : Const, decl : Definition | Opaque | Theorem, args : List[Expression]) -> Expression:
        decl_val = self.get_declaration_val_with_substituted_level_params(decl, fn.lvl_params)
        return fold_apps(decl_val, args)
    
    def delta_reduction(self, expr : Expression) -> Optional[Expression]:
        """ Unfolds the applications of the expression. If the function is a declaration, then it unfolds it. """
        is_d = self.is_delta(expr)
        if is_d is None: 
            return None
        ret = self.delta_reduction_core(*is_d)
        return ret
    
    def reduce_proj_core(self, proj_struct : Expression, idx : int) -> Optional[Expression]:
        """ If we have a projection of an expression that is an application of a constructor, then we reduce it to the corresponding argument of the constructor. 
        
        For example, proj 0 (Prod.mk (A) (B) (a : A) (b : B)) would be reduced to a. Note that in this case A B are parameters of the constructor, and a and b are the actual arguments, used in the projection.
        """
        if isinstance(proj_struct, StrLit): proj_struct = str_lit_to_constructor(self.environment, proj_struct)
        
        proj_struct_fn, proj_struct_args = unfold_app(proj_struct)
        if not isinstance(proj_struct_fn, Const): 
            return None
        constructor_decl = self.environment.get_declaration_under_name(proj_struct_fn.cname)
        if not isinstance(constructor_decl, Constructor): 
            return None

        if constructor_decl.num_params + idx >= len(proj_struct_args): 
            return None

        return proj_struct_args[constructor_decl.num_params + idx]
    
    def reduce_proj(self, proj : Proj, cheap_rec : bool, cheap_proj : bool) -> Optional[Expression]:
        idx = proj.index
        c = proj.expr
        # use whnf to unfold the definitions if cheap_proj is False
        c = self.whnf_core(c, cheap_rec=cheap_rec, cheap_proj=cheap_proj) if cheap_proj else self.whnf(c) 
        return self.reduce_proj_core(c, idx)
    
    def try_unfold_proj_app(self, e : Expression) -> Optional[Expression]: 
        f = get_app_function(e)
        if not isinstance(f, Proj): 
            return None
        e_new = self.whnf_core(e, cheap_rec=False, cheap_proj=False)
        if e_new == e: 
            return None
        return e_new
    
    def def_eq_args(self, t : Expression, s : Expression) -> bool:
        while isinstance(t, App) and isinstance(s, App):
            if not self.def_eq(t.arg, s.arg): 
                return False
            t = t.fn
            s = s.fn
        return (not isinstance(t, App)) and (not isinstance(s, App))

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
            if t_new is not None: t_n = t_new
            else: s_n = self.whnf_core(self.delta_reduction_core(*id_s), cheap_rec=False, cheap_proj=True)
        elif (id_t is not None) and (id_s is not None):
            hint_compare = compare_reducibility_hints(id_t[1], id_s[1])
            if hint_compare < 0: # reduce t
                t_n = self.whnf_core(self.delta_reduction_core(*id_t), cheap_rec=False, cheap_proj=True)
            elif hint_compare > 0: # reduce s
                s_n = self.whnf_core(self.delta_reduction_core(*id_s), cheap_rec=False, cheap_proj=True)
            else: # reduce both
                if isinstance(t_n, App) and isinstance(s_n, App) and (id_t[1] is id_s[1]) and isinstance(id_t, Definition) and isinstance(id_t.hint, Regular):
                    if not self.failure_cache.did_fail_before(t_n, s_n):
                        if self.def_eq_const(id_t[0], id_s[0]) and self.def_eq_args(t_n, s_n):
                            return t_n, s_n, ReductionStatus.EQUAL
                        else:
                            self.failure_cache.put(t_n, s_n)
                t_n = self.whnf_core(self.delta_reduction_core(*id_t), cheap_rec=False, cheap_proj=True)
                s_n = self.whnf_core(self.delta_reduction_core(*id_s), cheap_rec=False, cheap_proj=True)
        else:
            raise PanicError("Unreachable code reached in lazy_delta_reduction_step.")

        is_easy = self.def_eq_easy(t_n, s_n)
        if is_easy is not None:
            return t_n, s_n, (ReductionStatus.EQUAL if is_easy else ReductionStatus.NOT_EQUAL)
        else: 
            return t_n, s_n, ReductionStatus.CONTINUE

    def lazy_delta_reduction(self, t_n : Expression, s_n : Expression) -> Tuple[Expression, Expression, Optional[bool]]:
        while True:
            if not t_n.has_fvars and not s_n.has_fvars: 
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

            #print(f"reduced to {t_n} and {s_n}")

            if status == ReductionStatus.CONTINUE: continue
            elif status == ReductionStatus.EQUAL: 
                return t_n, s_n, True
            elif status == ReductionStatus.NOT_EQUAL: 
                return t_n, s_n, False
            elif status == ReductionStatus.UNKNOWN: 
                return t_n, s_n, None
            else: raise PanicError("Unknown reduction status.")

    def lazy_delta_proj_reduction(self, t_n : Expression, s_n : Expression, idx : int) -> bool:
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
                        return self.def_eq_core(t, s)
                return self.def_eq_core(t_n, s_n)
    
    def reduce_nat_lit(self, e : Expression) -> Optional[Expression]:
        if e.has_fvars: 
            return None
        
        fn, args = unfold_app(e)
        if not isinstance(fn, Const): 
            return None
        if len(args) == 0: # TODO: why does not lean kernel do this?
            if fn.cname == self.environment.Nat_zero_name: 
                return NatLit(0)
        if len(args) == 1:
            if fn.cname == self.environment.Nat_succ_name:
                arg = self.whnf(args[0])
                if isinstance(arg, NatLit): 
                    return NatLit(arg.val + 1)
                if isinstance(arg, Const) and arg.cname == self.environment.Nat_zero_name: 
                    return NatLit(1)
                return None
        if len(args) == 2:
            arg1 = self.whnf(args[0])
            if not isinstance(arg1, NatLit): 
                return None
            arg2 = self.whnf(args[1])
            if not isinstance(arg2, NatLit): 
                return None
            
            name = fn.cname
            if name == self.environment.Nat_add_name: 
                return reduce_bin_nat_op(nat_add, arg1.val, arg2.val)
            elif name == self.environment.Nat_sub_name: 
                return reduce_bin_nat_op(nat_sub, arg1.val, arg2.val)
            elif name == self.environment.Nat_mul_name: 
                return reduce_bin_nat_op(nat_mul, arg1.val, arg2.val)
            elif name == self.environment.Nat_pow_name: 
                return reduce_bin_nat_op(nat_pow, arg1.val, arg2.val)
            elif name == self.environment.Nat_gcd_name: 
                return reduce_bin_nat_op(nat_gcd, arg1.val, arg2.val)
            elif name == self.environment.Nat_mod_name: 
                return reduce_bin_nat_op(nat_mod, arg1.val, arg2.val)
            elif name == self.environment.Nat_div_name: 
                return reduce_bin_nat_op(nat_div, arg1.val, arg2.val)
            elif name == self.environment.Nat_eq_name: 
                return reduce_bin_nat_pred(self.environment, nat_beq, arg1.val, arg2.val)
            elif name == self.environment.Nat_le_name: 
                return reduce_bin_nat_pred(self.environment, nat_ble, arg1.val, arg2.val)
            elif name == self.environment.Nat_land_name: 
                return reduce_bin_nat_op(nat_land, arg1.val, arg2.val)
            elif name == self.environment.Nat_lor_name: 
                return reduce_bin_nat_op(nat_lor, arg1.val, arg2.val)
            elif name == self.environment.Nat_lxor_name: 
                return reduce_bin_nat_op(nat_xor, arg1.val, arg2.val)
            elif name == self.environment.Nat_shiftl_name: 
                return reduce_bin_nat_op(nat_shiftl, arg1.val, arg2.val)
            elif name == self.environment.Nat_shiftr_name: 
                return reduce_bin_nat_op(nat_shiftr, arg1.val, arg2.val)
        return None
    
    def quot_reduce_rec(self, e : Expression) -> Optional[Expression]:
        fn, args = unfold_app(e)
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

        mk_fn, mk_args = unfold_app(mk)

        if not isinstance(mk_fn, Const): 
            return None
        if mk_fn.cname != self.environment.Quot_mk_name: 
            return None
        if len(mk_args) != 3: 
            return None # the Quot.mk takes 3 arguments

        assert isinstance(mk, App)
        f = args[arg_pos] # get the function we are lifting/inducing
        r = App(f, mk.arg) # get the class representative and apply f on it

        elim_arity = mk_pos+1
        if len(args) > elim_arity:
            r = fold_apps(r, args[elim_arity:]) # reapply the arguments that were not relevant for the recursor
        return r
    
    def inductive_reduce_rec(self, e : Expression, cheap_rec : bool, cheap_proj : bool) -> Optional[Expression]:
        # Second unfold the application and get the recursor
        rec_fn, rec_args = unfold_app(e)
        if not isinstance(rec_fn, Const): 
            return None
        
        rec_decl = self.environment.get_declaration_under_name(rec_fn.cname)
        if not isinstance(rec_decl, Recursor): 
            return None

        major_index = rec_decl.get_major_index()

        if major_index >= len(rec_args): 
            return None
        major = rec_args[major_index]

        if rec_decl.isK:
            major = self.to_constructor_when_K(rec_decl, major, cheap_rec=cheap_rec, cheap_proj=cheap_proj)

        major = self.whnf_core(major, cheap_rec=cheap_rec, cheap_proj=cheap_proj) if cheap_rec else self.whnf(major) 
        if isinstance(major, NatLit):
            major = nat_lit_to_constructor(self.environment, major)
        elif isinstance(major, StrLit):
            major = str_lit_to_constructor(self.environment, major)
        else:
            major = self.to_constructor_when_structure(rec_decl.get_major_induct(), major, cheap_rec=cheap_rec, cheap_proj=cheap_proj)
        
        rule = rec_decl.get_recursion_rule(major)
        if rule is None: 
            return None

        _, major_args = unfold_app(major)
        if len(major_args) < rule.num_fields: 
            return None 
        if len(rec_fn.lvl_params) != len(rec_decl.lvl_params): 
            return None
        rhs = self.subst_level_params(rule.value, rec_decl.lvl_params, rec_fn.lvl_params) # clones the rule.value

        # apply parameters, motives and minor premises from recursor application.
        assert rec_decl.num_params + rec_decl.num_motives + rec_decl.num_minors < len(rec_args), "Recursor application does not have enough arguments."
        rhs = fold_apps(rhs, rec_args[:rec_decl.num_params + rec_decl.num_motives + rec_decl.num_minors]) # this is the actual reduction of the recursor

        #TODO : find what is the difference between params and indices

        # TODO: The number of parameters in the constructor is not necessarily
        #equal to the number of parameters in the recursor when we have
        #nested inductive types. 
        nparams = len(major_args) - rule.num_fields
        # apply fields from major premise
        assert nparams + rule.num_fields <= len(major_args), f"Major premise does not have the expected number of fields. Expected at least {nparams + rule.num_fields}, but got {len(major_args)}."
        selected_major_args = major_args[nparams: nparams + rule.num_fields]
        if len(selected_major_args) != rule.num_fields: raise RecursorError("Major premise does not have the expected number of fields.")
        rhs = fold_apps(rhs, selected_major_args) # reapply the indices' arguments back

        # the remaining arguments are not relevant for the recursor; they are just applied back to whatever we got from the reduction
        if len(rec_args) > major_index + 1: 
            rhs = fold_apps(rhs, rec_args[major_index + 1:])
        
        return rhs
    
    def reduce_recursor(self, e : Expression, cheap_rec : bool, cheap_proj : bool) -> Optional[Expression]:
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
        if not isinstance(e, App): 
            return None
        if not isinstance(e.arg, Const): 
            return None
        if isinstance(e.fn, Const) and e.fn.cname == self.environment.Bool_reduce_name:
            raise NotImplementedError("TODO")
            #object * r = ir::run_boxed(env, options(), const_name(arg), 0, nullptr);
            #if (!lean_is_scalar(r)) {
            #    lean_dec_ref(r);
            #    throw kernel_exception(env, "type checker failure, unexpected result value for 'Lean.reduceBool'");
            #}
            #return lean_unbox(r) == 0 ? some_expr(mk_bool_false()) : some_expr(mk_bool_true());
        if isinstance(e.fn, Const) and e.fn.cname == self.environment.Nat_reduce_name:
            raise NotImplementedError("TODO")
            #object * r = ir::run_boxed(env, options(), const_name(arg), 0, nullptr);
            #if (lean_is_scalar(r) || lean_is_mpz(r)) {
            #    return some_expr(mk_lit(literal(nat(r))));
            #} else {
            #    throw kernel_exception(env, "type checker failure, unexpected result value for 'Lean.reduceNat'");
            #}

    # WHNF
    def whnf_fvar(self, fvar : FVar, cheap_rec : bool, cheap_proj : bool) -> Expression:
        fvar_val = self.get_value_of_fvar(fvar) 
        if fvar_val is None:
            return fvar
        else:
            return self.whnf_core(fvar_val, cheap_rec=cheap_rec, cheap_proj=cheap_proj) 

    def whnf_core(self, expr : Expression, cheap_rec : bool, cheap_proj : bool) -> Expression:
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
            raw_fn, raw_args = unfold_app(expr)
            
            fn = self.whnf_core(raw_fn, cheap_rec=cheap_rec, cheap_proj=cheap_proj)
            if isinstance(fn, Lambda):
                r = self.whnf_core(self.beta_reduction(fn, raw_args), cheap_rec=cheap_rec, cheap_proj=cheap_proj)
            elif fn == raw_fn:
                r = self.reduce_recursor(expr, cheap_rec=cheap_rec, cheap_proj=cheap_proj)
                if r is not None: 
                    red = self.whnf_core(r, cheap_rec=cheap_rec, cheap_proj=cheap_proj)
                    return red
                else: 
                    return expr
            else:
                r = self.whnf_core(fold_apps(fn, raw_args), cheap_rec=cheap_rec, cheap_proj=cheap_proj)
        elif isinstance(expr, Let):
            r = self.whnf_core(self.instantiate(body=expr.body, val=expr.val), cheap_rec=cheap_rec, cheap_proj=cheap_proj)
        
        if r is None:
            raise PanicError(f"Expr of type {expr.__class__.__name__} could not be matched, this should not happen.")

        if (not cheap_rec) and (not cheap_proj): self.whnf_core_cache.put(expr, r)

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
            t1 = self.whnf_core(t, cheap_rec=False, cheap_proj=False)

            v = self.reduce_native(t1)
            if v is not None:
                # cache the result of native reduction
                self.whnf_cache.put(e, v)
                return v

            v = self.reduce_nat_lit(t1)
            if v is not None: 
                # cache the result of nat_lit reduction
                self.whnf_cache.put(e, v)
                return v
            
            next_t = self.delta_reduction(t1)
            if next_t is not None:
                t = next_t
            else:
                r = t1
                # cache the result if it was NOT delta reduced
                self.whnf_cache.put(e, r)
                return r

    # INFERENCE
    def infer_fvar(self, fvar : FVar):
        return self.get_type_of_fvar(fvar)
    
    def infer_app(self, app : App, infer_only : bool) -> Expression:
        if not infer_only:
            # the function should be a pi type
            fn_type = self.ensure_pi(self.infer_core(app.fn, infer_only=(self.allow_unstrict_infer and infer_only)))
            
            # get the type of the argument
            inferred_domain = self.infer_core(app.arg, infer_only=(self.allow_unstrict_infer and infer_only))

            # the domain of the function should be equal to the type of the argument
            if not self.def_eq(fn_type.domain, inferred_domain):
                raise ExpectedEqualExpressionsError(fn_type.domain, inferred_domain)
            
            infered_type = self.instantiate(body=fn_type.codomain, val=app.arg)
            return infered_type
        else:
            # If infer_only is true we only check that the type of fn is a pi type and keep substituting the arguments into the function type's codomain. We don't check that arguments match the function type's domain.
            fn, args = unfold_app(app)
            fn_type = self.infer_core(fn, infer_only=(self.allow_unstrict_infer and infer_only))
            
            j = 0
            for i in range(len(args)):
                if isinstance(fn_type, Pi):
                    fn_type = fn_type.codomain
                else:
                    fn_type = self.instantiate_multiple(fn_type, args[j:i:-1]) # TODO: check if -1 is correct
                    fn_type = self.ensure_pi(fn_type)
                    fn_type = fn_type.codomain
            
            return self.instantiate_multiple(fn_type, args[j::-1]) # TODO: check if -1 is correct
            
    def infer_sort(self, sort : Sort) -> Expression:
        return Sort(LevelSucc(sort.level))
    
    def infer_pi(self, pi : Pi, infer_only : bool) -> Expression:
        fvars : List[FVar] = []
        us : List[Level] = []
        e = pi
        while isinstance(e, Pi):
            inst_domain = self.instantiate_multiple(e.domain, tuple(fvars[::-1]))
            t1 = self.ensure_sort(self.infer_core(inst_domain, infer_only))
            us.append(t1.level)
            fvars.append(self.create_fvar(e.bname, inst_domain, None, False))
            e = e.codomain

        e = self.instantiate_multiple(e, tuple(fvars[::-1]))
        t1 = self.ensure_sort(self.infer_core(e, infer_only))
        lvl = t1.level
        for u in us[::-1]:
            lvl = make_imax(u, lvl)

        for fvar in fvars[::-1]:
            self.remove_fvar(fvar)

        return Sort(level=lvl)
    
    def infer_const(self, c : Const) -> Expression:
        if len(c.lvl_params) != len(self.environment.get_declaration_under_name(c.cname).lvl_params):
            raise PanicError("The number of level parameters of the constant does not match the number of level parameters in the environment.")
        return self.get_declaration_type_with_substituted_level_params(self.environment.get_declaration_under_name(c.cname), c.lvl_params)

    def make_pi_binding(self, fvars : List[FVar], b : Expression) -> Expression:
        r = abstract_multiple_bvars(fvars[::-1], b)
        for i in range(len(fvars)-1, -1, -1):
            c_fvar = fvars[i]
            assert c_fvar.is_let == False, "Cannot have a let binding in a pi binding."
            abs_type = abstract_multiple_bvars(fvars[:i][::-1], c_fvar.type)
            r = Pi(c_fvar.name, abs_type, r)
        
        return r

    def infer_lambda(self, lam : Lambda, infer_only : bool) -> Expression:
        fvars : List[FVar] = []
        e = lam

        while isinstance(e, Lambda):
            inst_domain = self.instantiate_multiple(e.domain, fvars[::-1])
            fvars.append(self.create_fvar(e.bname, inst_domain, None, False))
            if not infer_only:
                self.ensure_sort(self.infer_core(inst_domain, infer_only))
            e = e.body
        
        r = self.instantiate_multiple(e, fvars[::-1])
        assert not r.has_loose_bvars
        r = self.infer_core(r, infer_only)
        r = self.cheap_beta_reduce(r)

        r = self.make_pi_binding(fvars, r)

        for fvar in fvars[::-1]:
            self.remove_fvar(fvar)
        return r
    
    def infer_nat_lit(self, n : NatLit) -> Expression:
        return Const(self.environment.Nat_name, [])
    
    def infer_string_lit(self, s : StrLit) -> Expression:
        return Const(self.environment.String_name, [])

    def make_let_binding(self, fvars : List[FVar], b : Expression) -> Expression:
        r = abstract_multiple_bvars(fvars[::-1], b)
        for i in range(len(fvars)-1, -1, -1):
            c_fvar = fvars[i]
            assert c_fvar.is_let == True, "Cannot have a non-let binding in a let binding."
            assert c_fvar.val is not None, "Cannot have a let binding without a value."

            abs_type = abstract_multiple_bvars(fvars[:i][::-1], c_fvar.type)
            abs_val = abstract_multiple_bvars(fvars[:i][::-1], c_fvar.val)

            r = Let(bname=c_fvar.name, domain=abs_type, val=abs_val, body=r)
        
        return r
    
    def infer_let(self, let : Let, infer_only : bool) -> Expression: # TODO check again
        fvars : List[FVar] = []
        vals : List[Expression] = []

        e = let
        while isinstance(e, Let):
            val_type = self.instantiate_multiple(e.domain, fvars[::-1])
            val = self.instantiate_multiple(e.val, fvars[::-1])
            fvars.append(self.create_fvar(e.bname, val_type, val=val, is_let=True))
            vals.append(val)

            if not infer_only:
                self.ensure_sort(self.infer_core(val_type, infer_only))
                inferred_val_type = self.infer_core(val, infer_only)

                if not self.def_eq(val_type, inferred_val_type):
                    raise ExpectedEqualExpressionsError(val_type, inferred_val_type)
            
            e = e.body
        
        r = self.instantiate_multiple(e, fvars[::-1])
        r = self.infer_core(r, infer_only)
        r = self.cheap_beta_reduce(r)
        used = [False] * len(fvars)

        mark_used(fvars, r, used)
        for i in range(len(fvars)-1, -1, -1):
            if not used[i]: # if the i-th fvar is not used in the r (the body of the let binding) then we don't need to check which other fvars are used in the value of it
                # go through and mark all the fvars that are used in the value of the i-th let binding
                # since for i-th fvars i+1, ..., n-th fvars are not used, we don't need to check them
                mark_used(fvars[:i], vals[i], used)
        
        used_fvars : List[FVar] = []
        for i in range(len(fvars)):
            if used[i]:
                used_fvars.append(fvars[i])
        
        r = self.make_let_binding(used_fvars, r)

        for fvar in fvars[::-1]:
            self.remove_fvar(fvar)
        return r


    def infer_proj(self, proj : Proj, infer_only : bool) -> Expression: # TODO: check again
        struct_type = self.infer_core(proj.expr, infer_only=(self.allow_unstrict_infer and infer_only))
        struct_type = self.whnf(struct_type)

        inductive_fn, args = unfold_app(struct_type)
        if not isinstance(inductive_fn, Const):
            raise ProjectionError(f"Expected a constant when unfolding the struct type for projection but got {inductive_fn.__class__}")
        if inductive_fn.cname != proj.sname:
            raise ProjectionError(f"Expected the struct name to be {proj.sname} but got {inductive_fn.cname}")
        I_name = inductive_fn.cname

        I_decl = self.environment.get_declaration_under_name(I_name)
        if not isinstance(I_decl, Inductive):
            raise ProjectionError(f"Expected an inductive type when unfolding the struct type for projection but got {I_decl} which is a {I_decl.__class__}")
        
        if I_decl.number_of_constructors != 1:
            raise ProjectionError(f"Expected the inductive type {I_name} to have exactly one constructor but got {I_decl.number_of_constructors}")
        
        if len(args) != I_decl.num_params + I_decl.num_indices:
            raise ProjectionError(f"Expected the {I_decl.num_params + I_decl.num_indices} arguments but got {len(args)}, when unfolding the struct type for projection.")

        constructor_decl = self.environment.get_declaration_under_name(I_decl.constructor_names[0])

        if not isinstance(constructor_decl, Constructor):
            raise DeclarationError(f"Expected a constructor declaration for the first constructor of the inductive type {I_name} but got {constructor_decl} which is a {constructor_decl.__class__}")

        assert constructor_decl.num_params == I_decl.num_params, "Sanity check failed: number of parameters in inductive type and constructor do not match."

        r = self.subst_level_params(constructor_decl.type, I_decl.lvl_params, inductive_fn.lvl_params)
        
        for i in range(I_decl.num_params):
            if i >= len(args):
                raise ProjectionError(f"Ran out of arguments when instantiating projection args.")
            r = self.whnf(r)
            if not isinstance(r, Pi):
                raise ProjectionError(f"Expected a Pi type when instantiating projection args but got {r.__class__}")
            r = self.instantiate(body=r.codomain, val=args[i])
        
        is_prop_type = self.is_prop(r)

        for i in range(proj.index):
            r = self.whnf(r)
            if not isinstance(r, Pi):
                raise ProjectionError(f"Expected a Pi type when reducing projection indices but got {r.__class__}")
            
            if r.codomain.has_loose_bvars: # TODO is this ok?
                r = self.instantiate(
                    body=r.codomain, 
                    val=Proj(I_name, i, proj.expr)
                )
                if is_prop_type and not self.is_prop(r):
                    raise ProjectionError(f"When substituting proj indices, the body should remain a prop type.")
            else:
                r = r.codomain
        
        r = self.whnf(r)
        if not isinstance(r, Pi):
            raise ProjectionError(f"Expected a Pi type for projection index but got {r.__class__}")

        r = r.domain

        if is_prop_type and not self.is_prop(r):
            raise ProjectionError(f"The prop should remain a prop type after reducing the projection index.")

        return r

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
        if expr.has_loose_bvars:
            raise UnboundVariableError("Cannot infer the type of an expression with unbound variables.")

        # check if expression is already in infer_cache (separate cache for infer_only)
        cached_inferred_type = self.infer_cache[infer_only].get(expr)
        if cached_inferred_type is not None: 
            return cached_inferred_type

        if isinstance(expr, BVar): 
            raise PanicError("Unreachable code reached: BVar in infer_core.")
        elif isinstance(expr, FVar): 
            inferred_type = self.infer_fvar(expr)
        elif isinstance(expr, MVar): 
            raise UnfinishedExpressionError("Cannot infer the type of an expression with metavariables.")
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
        
        # cache the result
        self.infer_cache[infer_only].put(expr, inferred_type)

        return inferred_type
    
    def clear_caches(self):
        self.whnf_cache.clear()
        self.whnf_core_cache.clear()
        self.infer_cache[False].clear()
        self.infer_cache[True].clear()
        self.equiv_manager.clear()
        self.instantiation_cache.clear()
        self.instantiation_multiple_cache.clear()
        self.failure_cache.clear()
        self.lvl_param_subst_cache.clear()

    def infer(self, expr : Expression, clear_caches : bool = True) -> Expression:
        if not self.local_context.is_empty():
            raise PanicError(f"Local context is not empty when inferring: {self.local_context}")
        
        if clear_caches:
            self.clear_caches()

        inferred_type = self.infer_core(expr, infer_only=(self.allow_unstrict_infer and False))
        return inferred_type
    
    # DECLARATION CHECKING
    def check_declaration_info(self, decl : Declaration):
        if not are_unique_level_params(decl.lvl_params):
            raise EnvironmentError(f"Level parameters in declaration info {decl.info} are not unique.")
        if decl.type.has_fvars:
            raise EnvironmentError(f"Type in declaration info {decl.info} contains free variables.")

        inferred_type = self.infer(decl.type)
        
        if not isinstance(inferred_type, Sort):
            raise EnvironmentError(f"Type of declaration info {decl.info} is not a sort.")
        
    def check_declaration_value(self, decl : Declaration):
        if not (isinstance(decl, Definition) or isinstance(decl, Theorem) or isinstance(decl, Opaque)):
            raise DeclarationError(f"Declaration {decl} is not a Definition, Theorem, or Opaque, when checking declaration value. It is a {decl.__class__.__name__}.")

        inferred_type = self.infer(decl.value)
        if not self.def_eq(inferred_type, decl.info.type):
            raise DeclarationError(f"Declaration {decl} ({decl.__class__.__name__}) has type {decl.info.type} but inferred type {inferred_type}") 

    def add_definition(self, d : Definition, type_check : bool = True):
        if type_check:
            self.check_declaration_info(d)
            self.check_declaration_value(d)
        self.environment.add_declaration(d)

    def add_theorem(self, t : Theorem, type_check : bool = True):
        if type_check:
            self.check_declaration_info(t)
            self.check_declaration_value(t)
        self.environment.add_declaration(t)

    def add_opaque(self, o : Opaque, type_check : bool = True):
        if type_check:
            self.check_declaration_info(o)
            self.check_declaration_value(o)
        self.environment.add_declaration(o)

    def add_axiom(self, a : Axiom, type_check : bool = True):
        if type_check:
            self.check_declaration_info(a)
        self.environment.add_declaration(a)
    
    def add_inductive(self, ind : Inductive, type_check : bool = True):
        self.environment.add_declaration(ind)

        if type_check:
            self.check_inductive_declaration_infos(ind.name)

    def add_constructor(self, constructor : Constructor, type_check : bool = True):
        self.environment.add_declaration(constructor)

        if type_check:
            self.check_inductive_declaration_infos(constructor.inductive_name)

    def number_of_added_constructors(self, inductive_decl : Inductive) -> int:
        count = 0
        for constructor_name in inductive_decl.constructor_names:
            if self.environment.exists_declaration_under_name(constructor_name):
                constructor_decl = self.environment.get_declaration_under_name(constructor_name)
                if not isinstance(constructor_decl, Constructor): raise DeclarationError(f"Inductive type's constructor name {inductive_decl.name} refers to a non-constructor {constructor_name}.")
                count += 1
        return count
    
    def add_quotient(self, q : Quot, type_check : bool = True):
        if type_check:
            self.check_declaration_info(q)
        self.environment.add_declaration(q)
    
    def check_inductive_declaration_infos(self, inductive : Name):
        """
        Inductive types are special in that they are defined cyclically: the constructors and the inductive type refer to each other cyclically. Thus we cannot check them as they are added to the environment. Instead, we check them once each part of the inductive definition has been added to the environment. We mark the inductive type and its constructors as checked once they have been successfully checked.
        """
        # First check that all the constructors have been added
        if not self.environment.exists_declaration_under_name(inductive): return
        inductive_decl = self.environment.get_declaration_under_name(inductive)
        if not isinstance(inductive_decl, Inductive):
            raise DeclarationError(f"Inductive type {inductive} not found.")
        
        found_constructors = self.number_of_added_constructors(inductive_decl)
        if found_constructors < inductive_decl.number_of_constructors: return
        assert(found_constructors == inductive_decl.number_of_constructors), "Sanity check failed: number of found constructors does not match the number of expected constructors."

        self.environment.checking_inductive = False # TODO: set this to true and debug
        # After all the constructors have been added, we can check the inductive type and its constructors
        self.check_declaration_info(inductive_decl)

        # Now check that the inductive type
        for i, constructor_name in enumerate(inductive_decl.constructor_names):
            constructor_decl = self.environment.get_declaration_under_name(constructor_name)
            self.check_declaration_info(constructor_decl)
            if not isinstance(constructor_decl, Constructor):
                raise DeclarationError(f"Sanity check failed: constructor {constructor_name} is not a constructor.")

            if i != constructor_decl.c_index:
                raise DeclarationError(f"Constructor {constructor_name} has index {constructor_decl.c_index} but should have index {i}.")

            if inductive_decl.num_params != constructor_decl.num_params:
                raise DeclarationError(f"Constructor {constructor_name} has {constructor_decl.num_params} parameters but the inductive type {constructor_decl.inductive_name} has {inductive_decl.num_params} parameters.")

        # Finally chec 
        inductive_decl.is_checked = True
        for constructor_name in inductive_decl.constructor_names:
            constructor_decl = self.environment.get_declaration_under_name(constructor_name)
            self.check_declaration_info(constructor_decl)
            if not isinstance(constructor_decl, Constructor):
                raise PanicError(f"Unreachable code reached: constructor {constructor_name} is not a constructor.")
            constructor_decl.is_checked = True # CHANGES INDUCTIVE, BUT THIS IS OK
        self.environment.checking_inductive = False # CHANGES INDUCTIVE, BUT THIS IS OK

    def add_recursor(self, recursor : Recursor, type_check : bool = True):
        if type_check:
            self.check_declaration_info(recursor)
        self.environment.add_declaration(recursor) # add the recursor to the environment before checking the recursion rules, since they refer to the recursor

        for rec_rule in recursor.recursor_rules:
            constructor_decl = self.environment.get_declaration_under_name(rec_rule.constructor)
            if not isinstance(constructor_decl, Constructor):
                raise DeclarationError(f"Recursor rule {rec_rule} is not associated with a constructor; found {constructor_decl.__class__.__name__} with name {constructor_decl.info.ciname} instead.")

    def add_declaration(self, decl : Declaration, type_check : bool = True):
        print(f"Adding declaration {decl.name}")
        if isinstance(decl, Definition): self.add_definition(decl, type_check)
        elif isinstance(decl, Theorem): self.add_theorem(decl, type_check)
        elif isinstance(decl, Opaque): self.add_opaque(decl, type_check)
        elif isinstance(decl, Axiom): self.add_axiom(decl, type_check)
        elif isinstance(decl, Inductive): self.add_inductive(decl, type_check)
        elif isinstance(decl, Constructor): self.add_constructor(decl, type_check)
        elif isinstance(decl, Recursor): self.add_recursor(decl, type_check)
        elif isinstance(decl, Quot): self.add_quotient(decl, type_check)
        else: raise DeclarationError(f"Unknown declaration type {decl.__class__.__name__}")