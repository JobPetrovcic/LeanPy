from typing import List, Optional, Tuple

from typeguard import typechecked
from Structures.Environment.Declaration import Axiom, Constructor, Declaration, DeclarationInfo, Definition, InductiveType, Opaque, Recursor, Theorem
from Structures.Environment.DeclarationManipulation import is_structural_inductive
from Structures.Environment.Environment import Environment
from Structures.Environment.LocalContext import LocalContext
from Structures.Expression.Expression import *
from Structures.Expression.ExpressionManipulation import abstract_bvar, clone_expression, do_fn, fold_apps, has_loose_bvars, has_specific_fvar, instantiate_bvar, has_fvars, level_zip, nat_lit_to_constructor, str_lit_to_constructor, substitute_level_params_in_expression, unfold_app, get_app_function
from Structures.Expression.Level import *
from Structures.Expression.LevelManipulation import antisymm_eq, antisymm_eq_list, are_unique_level_params, clone_level, is_zero_level
from Structures.KernelErrors import ExpectedDifferentExpressionError, ExpectedDifferentTypesError, PanicError, ProjectionError, EnvironmentError, DeclarationError
from Structures.Name import Name
import warnings

#TODO s:
# - special cases for Nat and String literals
# - quot
# - level cloning

def dprint(s : str):
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
    @typechecked
    def remove_fvar(self, fvar: FVar):
        self.local_context.remove_fvar(fvar)
    
    @typechecked
    def get_type_of_fvar(self, fvar : FVar) -> Expression:
        return self.local_context.get_fvar_type(fvar, use_same_fvars=True)
    
    @typechecked
    def get_value_of_fvar(self, fvar : FVar) -> Optional[Expression]:
        return self.local_context.get_fvar_value(fvar, use_same_fvars=True)
    
    @typechecked
    def instantiate(self, body : Expression, val : Expression, clone_body : bool, clone_val : bool, use_same_fvars : bool = True) -> Expression:
        """
        Replace the outermost bound variable in the body with the value. Clones the body if needed.
        If clone_val is true, then the value is cloned EVERY TIME it is used.
        """
        return instantiate_bvar(body, val, clone_body=clone_body, clone_val=clone_val, use_same_fvars=use_same_fvars)
    
    @typechecked
    def create_fvar(self, name: Name, type: Expression, val : Optional[Expression], is_let : bool) -> FVar:
        fvar = FVar(name, type, val, is_let=is_let)
        self.local_context.add_fvar(fvar)
        return fvar

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
    @typechecked
    def is_structure_like(self, decl_name : Name) -> bool:
        decl = self.environment.get_declaration_under_name(decl_name)
        if not isinstance(decl, InductiveType): return False
        return is_structural_inductive(decl) and decl.num_indices == 0 and not decl.is_recursive
    
    @typechecked
    def is_prop(self, e : Expression, clone : bool):
        inferred_type = self.whnf(self.infer_core(e, clone=clone, infer_only=True), clone=False, unfold_definition=True)
        return isinstance(inferred_type, Sort) and is_zero_level(inferred_type.level)

    # DEFINITIONAL EQUALITY
    @typechecked
    def def_eq_sort(self, l : Sort, r : Sort) -> bool:
        """Sorts are equal if their levels satisfy antisymmetry.
        The comparsion function does not change anything, so def_eq_sort is safe to use when passing by reference.
        """
        return antisymm_eq(l.level, r.level)

    @typechecked
    def def_eq_const(self, l : Const, r : Const) -> bool:
        """
        If the names are the same, and the level parameters are equal, then the constants are equal.
        Since nothing is changed, this function is safe to use when passing by reference.
        """
        return l.name == r.name and antisymm_eq_list(l.lvl_params, r.lvl_params)

    @typechecked
    def def_eq_bvar(self, l : BVar, r : BVar) -> bool:
        raise PanicError("BVar should have been substituted by now, when comparing expressions for definitional equality.")

    @typechecked
    def def_eq_fvar(self, l : FVar, r : FVar) -> bool:
        """
        For FVars, we are using the "is" operator to compare them. 
        They are only a place holder for the actual type, so this is enough. However, care must be taken when cloning.
        """
        return l is r

    @typechecked
    def def_eq_app(self, l : App, r : App, clone : bool) -> bool:
        f_fn, f_args = unfold_app(l.fn)
        g_fn, g_args = unfold_app(r.fn)
        if not self.def_eq(f_fn, g_fn, clone=clone):
            return False
        
        if len(f_args) != len(g_args): return False
        for f_arg, g_arg in zip(f_args, g_args):
            if not self.def_eq(f_arg, g_arg, clone=clone):
                return False
        return True

    @typechecked
    def def_eq_pi(self, l: Pi, r: Pi, clone : bool) -> bool:
        if not self.def_eq(l.arg_type, r.arg_type, clone=True): # we have to clone the argument type since it is used later
            return False
        
        fvar, (l_n, r_n) = self.instantiate_fvar_multiple_bodies(
            bname=l.bname, 
            arg_type=l.arg_type, 
            arg_val=None, 
            bodies=[l.body_type, r.body_type], 
            clone=clone, 
        )
        
        result = self.def_eq(l_n, r_n, clone=False) # n_l and n_r are (possibly) already separated from l and r when instantiated, so def_eq can do whatever it wants
        self.remove_fvar(fvar)
        return result

    @typechecked
    def def_eq_lambda(self, l : Lambda, r : Lambda, clone : bool) -> bool: # CLONE CHECKED
        if not self.def_eq(l.arg_type, r.arg_type, clone=True): # we have to clone the argument type since it is used later
            return False
        
        fvar, (l_n, r_n) = self.instantiate_fvar_multiple_bodies(
            bname=l.bname, 
            arg_type=l.arg_type, 
            arg_val=None,
            bodies=[l.body, r.body], 
            clone=clone
        )
        ret = self.def_eq(l_n, r_n, clone=False) # n_l and n_r are already separated from l and r when instantiated, so def_eq can do whatever it wants
        self.remove_fvar(fvar)
        return ret

    @typechecked
    def try_structural_eta_expansion_core(self, t : Expression, s : Expression, clone : bool) -> bool:
        # First part: deconstruct s and ensure it
        s_fn, s_args = unfold_app(s)

        if not isinstance(s_fn, Const): return False
        
        decl = self.environment.get_declaration_under_name(s_fn.name)
        if not isinstance(decl, Constructor): return False
        if len(s_args) != decl.num_params + decl.num_fields: return False
        if not self.is_structure_like(decl.inductive_name): return False

        if not self.def_eq(
            self.infer_core(t, clone=True, infer_only=True), # clone since we use t later
            self.infer_core(s, clone=True, infer_only=True), # clone since we use s later
            clone=False
        ): return False

        use_t = clone_expression(t, use_same_fvars=True) if clone else t
        for i in range(decl.num_params, len(s_args)):
            # TODO: what name should be used here?
            proj = Proj(type_name=decl.inductive_name, index=i-decl.num_params, struct=use_t)
            use_s_arg_i = clone_expression(s_args[i], use_same_fvars=True) if clone else s_args[i]

            if not self.def_eq(proj, use_s_arg_i, clone=False): return False
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
        return self.def_eq(use_t, new_s, clone=False)

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
        elif isinstance(l, Const) and isinstance(r, Const):
            return self.def_eq_const(l, r)
        elif isinstance(l, BVar) and isinstance(r, BVar):
            return self.def_eq_bvar(l, r)
        elif isinstance(l, FVar) and isinstance(r, FVar):
            return self.def_eq_fvar(l, r)

    def def_eq(self, l: Expression, r: Expression, clone : bool) -> bool:
        if l is r: return True
        
        #lid = id(l)
        #rid = id(r)
        ##dprint(f"l {lid}: {l} {l.__class__}")
        ##dprint(f"r {rid}: {r} {r.__class__}")

        is_easy = self.def_eq_easy(l, r) # no cloning needed
        if is_easy is not None: return is_easy
        
        l_n = self.whnf(l, clone=clone, unfold_definition=True)
        r_n = self.whnf(r, clone=clone, unfold_definition=True)
        ##dprint(f"l_n {lid}: {l_n}")
        ##dprint(f"r_n {rid}: {r_n}")

        is_easy = self.def_eq_easy(l_n, r_n)
        if is_easy is not None: return is_easy
        
        if isinstance(l_n, App) and isinstance(r_n, App):
            if self.def_eq_app(l_n, r_n, clone=True): return True
        elif isinstance(l_n, Pi) and isinstance(r_n, Pi):
            if self.def_eq_pi(l_n, r_n, clone=True): return True
        elif isinstance(l_n, Lambda) and isinstance(r_n, Lambda):
            if self.def_eq_lambda(l_n, r_n, clone=True): return True

        # Reductions
        if self.try_structural_eta_expansion(l_n, r_n, True):
            return True
        if self.try_eta_expansion(l_n, r_n, False): # l_n and r_n are already whnfed and so cloned, therefore, try_eta_expansion can do whatever it wants
            return True

        return False
    
    # REDUCTION
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
        raise NotImplementedError("delete this")
        _, sub_expr = self.instantiate_fvar( # for let expression we use fvars; it is up to the wnhf to further unfold the fvar later
            bname=expr.bname,
            arg_type=expr.arg_type,
            arg_val=expr.val, 
            body=expr.body, 
            clone=clone, 
            is_let=True
        )
        return sub_expr

    @typechecked
    def is_delta(self, c : Const) -> Optional[Expression]: # CLONE CHECKED
        """Returns the value of the constant if it can be unfolded, otherwise return None."""
        decl = self.environment.get_declaration_under_name(c.name)
        if not decl.has_value():
            return None
        
        #TODO use reducibility hints
        assert isinstance(decl, Definition) or isinstance(decl, Opaque) or isinstance(decl, Theorem)
        return self.environment.get_cloned_val_with_substituted_level_params(decl, c.lvl_params)
    
    @typechecked
    def delta_reduction(self, expr : Expression, clone : bool) -> Optional[Expression]: # CLONE CHECKED
        """ Unfolds the definition until the function is no longer an application of a function that is also a constant."""
        expr = clone_expression(expr, use_same_fvars=True) if clone else expr

        fn, args = unfold_app(expr)
        if not isinstance(fn, Const):
            return None
        
        unfolded_fn = self.is_delta(fn)
        if unfolded_fn is None: return None
        return fold_apps(unfolded_fn, args)
    
    @typechecked
    def reduce_proj_core(self, proj_struct : Expression, idx : int) -> Optional[Expression]: # CLONE CHECKED
        """ If we have a projection of an expression that is an application of a constructor, then we reduce it to the corresponding argument of the constructor. 
        
        So proj 0 (Prod.mk (A) (B) (a : A) (b : B)) would be reduced to a. Note that in this case A B are parameters of the constructor, and a b are the actual arguments, used in the projection.
        """
        if isinstance(proj_struct, StringLit):
            raise NotImplementedError("String literals are not implemented yet.")
        
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

    #inductive stuff
    @typechecked
    def get_first_constructor(self, inductive_name : Name) -> Optional[Constructor]: # CLONE CHECKED
        decl = self.environment.get_declaration_under_name(inductive_name)
        if not isinstance(decl, InductiveType): return None
        if decl.number_of_constructors() == 0: return None
        return self.environment.get_constructor(decl.constructor_names[0])
    
    # inductive stuff
    @typechecked
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
    @typechecked
    def mk_nullary_constructor(self, type_e : Expression, num_params : int) -> Optional[Expression]:
        d, args = unfold_app(type_e)
        if not isinstance(d, Const): return None
        constructor = self.get_first_constructor(d.name)
        if constructor is None: return None
        args = args[:num_params]
        return fold_apps(Const(name=constructor.info.name, lvl_params=d.lvl_params), args)

    # inductive stuff
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

        if not self.def_eq(app_type, new_type, clone=False): # both cloned so no need to clone
            return e
        return new_constructor_app
    
    # inductive stuff
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
        ##dprint(f"major_idx {major_idx}")
        if major_idx >= len(rec_args): return None
        major = rec_args[major_idx]
        ##dprint(f"major before {major}")

        ##dprint(f"rec_decl {rec_decl}")
        if rec_decl.isK:
            #major = self.to_constructor_when_K(rec_decl, major)
            # TODO : what is going on here?
            warnings.warn("K-style recursion not fully implemented yet")

        ##dprint(f"rec_decl {rec_decl.info.name}")
        #for i, arg in enumerate(rec_args):
        #    #dprint(f"arg {i} {arg}")
        ##dprint(f"major {major}")

        major = self.whnf(major, clone=False, unfold_definition=True)
        if isinstance(major, NatLit):
            major = nat_lit_to_constructor(major)
        elif isinstance(major, StringLit):
            major = str_lit_to_constructor(major)
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
        
        ##dprint(f"rhs {rhs}")
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
                ##dprint(f"rr {expr}")
                r = self.reduce_recursor(expr)
                if r is not None: 
                    red = self.whnf_core(r, clone=False, cheap_proj=cheap_proj)
                    ##dprint(f"red {red}")
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
            unfolded = self.delta_reduction(expr, clone=False)
            if unfolded is None:
                return expr
            expr = self.whnf_core(unfolded, clone=False, cheap_proj=False) # we do not clone the unfolded expression since the initial whnf_core already clones it
        return expr

    # TYPE INFERENCE
    def infer_fvar(self, fvar : FVar):
        return self.get_type_of_fvar(fvar)
        
    def infer_app(self, app : App, clone : bool, infer_only : bool) -> Expression:
        if infer_only:
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
        else:
            # the function should be a pi type
            whnfd_fn_type = self.whnf(self.infer_core(app.fn, clone=clone, infer_only=infer_only), clone=False, unfold_definition=False)
            if not isinstance(whnfd_fn_type, Pi):
                raise ExpectedDifferentExpressionError(Pi, whnfd_fn_type.__class__)
            
            # get the type of the argument
            inferred_arg_type = self.infer_core(app.arg, clone=True, infer_only=infer_only)

            #has_fvar_not_in_context(inferred_arg_type, self.local_context) # TODO : remove this after testing
            #has_fvar_not_in_context(whnfd_fn_type.arg_type, self.local_context) # TODO : remove this after testing
            # the domain of the function should be equal to the type of the argument
            if not self.def_eq(whnfd_fn_type.arg_type, inferred_arg_type, clone=False):
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
        if infer_only:
            raise NotImplementedError("Infer only optimization not implemented yet")
        else:
            lhs = self.infer_sort_of(pi.arg_type, clone=clone)

            fvar, inst_body_type = self.instantiate_fvar(
                bname=pi.bname, 
                arg_type=pi.arg_type, 
                arg_val=None,
                body=pi.body_type, 
                clone=clone
            )
            rhs = self.infer_sort_of(inst_body_type, clone=False)
            self.remove_fvar(fvar)

            return Sort(LevelIMax(lhs, rhs))
    
    def infer_sort_of(self, e : Expression, clone : bool) -> Level:
        whnf_d_e_type = self.whnf(self.infer_core(e, clone=clone, infer_only=False), clone=False, unfold_definition=False)
        if isinstance(whnf_d_e_type, Sort):
            return whnf_d_e_type.level
        raise ExpectedDifferentExpressionError(Sort, whnf_d_e_type.__class__)
    
    def infer_lambda(self, e : Lambda, clone : bool, infer_only : bool) -> Expression:
        if not infer_only:
            self.infer_sort_of(e.arg_type, clone=True)
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
            self.infer_sort_of(e.arg_type, clone=True) # have to clone the arg_type since we are using it 
            inferred_val_type = self.infer_core(e.val, clone=True, infer_only=infer_only) # have to clone the val since we are using it
            cloned_arg_type = clone_expression(e.arg_type, use_same_fvars=True) if clone else e.arg_type
            if not self.def_eq(inferred_val_type, cloned_arg_type, clone=False):
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
        struct_type = self.whnf(self.infer_core(proj.struct, clone=clone, infer_only=infer_only), clone=False, unfold_definition=False)
        inductive_name, args = unfold_app(struct_type)
        if not isinstance(inductive_name, Const): return None
        if inductive_name.name != proj.type_name: return None
        
        inductive_decl = self.environment.get_inductive(inductive_name.name)
        if inductive_decl.number_of_constructors() != 1: return None
        if len(args) != inductive_decl.num_params + inductive_decl.num_indices: return None
        
        constructor_decl = self.environment.get_constructor(inductive_decl.constructor_names[0]) # there is only one canonical constructor
        return inductive_name, inductive_decl, constructor_decl, args

    def infer_proj(self, proj : Proj, clone : bool, infer_only : bool) -> Expression:
        proj_index = proj.index

        pos_cons = self.proj_get_constructor(proj, clone=clone, infer_only=infer_only)
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
        return Const(self.environment.get_nat_name(), [])
    
    def infer_string_lit(self, s : StringLit) -> Expression:
        return Const(self.environment.get_string_name(), [])

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
        try:
            has_fvar_not_in_context(inferred_type, self.local_context) # TODO : remove this after testing
        except Exception as e:
            #dprint(f"EXPRESSION ({expr_class}) ({infer_only}) : {expr}")
            raise e

        return inferred_type
    @typechecked
    def infer(self, expr : Expression, clone : bool) -> Expression:
        if not self.local_context.is_empty():
            raise PanicError("Local context is not empty when inferring.")
        print("CHECKING NEW EXPRESSION", expr)
        inferred_type = self.infer_core(expr, clone=clone, infer_only=False)

        self.local_context.clear()

        has_fvar_not_in_context(inferred_type, self.local_context) # TODO : remove this after testing
        return inferred_type

    # CHECKING DECLARATIONS
    @typechecked
    def check_declar_info(self, info: DeclarationInfo):
        if not are_unique_level_params(info.lvl_params):
            raise EnvironmentError(f"Level parameters in declaration info {info} are not unique.")
        if has_fvars(info.type):
            raise EnvironmentError(f"Type in declaration info {info} contains free variables.")
        
        inferred_type = self.infer_core(info.type, clone=True, infer_only=True)
        self.ensure_sort(inferred_type)

    def ensure_sort(self, e: Expression) -> Level:
        if isinstance(e, Sort):
            return e.level
        # TODO: is reduction ok here?
        #whnfd_expr = self.whnf(e)
        #if isinstance(whnfd_expr, Sort):
        #    return whnfd_expr.level
        raise PanicError("ensure_sort could not produce a sort")
    
    @typechecked
    def check_declaration_info(self, info : DeclarationInfo):
        if not are_unique_level_params(info.lvl_params):
            raise EnvironmentError(f"Level parameters in declaration info {info} are not unique.")
        if has_fvars(info.type):
            raise EnvironmentError(f"Type in declaration info {info} contains free variables.")

        inferred_type = self.infer(info.type, clone=True)
        self.ensure_sort(inferred_type)

    @typechecked
    def add_definition(self, name : Name, d : Definition):
        print("ADDING DEFINITION : ", name)
        self.check_declaration_info(d.info)

        infered_type = self.infer(d.value, clone=True)
        clone_d_info_type = clone_expression(d.info.type, use_same_fvars=True)
        if not self.def_eq(infered_type, clone_d_info_type, clone=False):
            raise DeclarationError(f"Definition {name} has type {d.info.type} but inferred type {infered_type}")
        self.environment.add_declaration(name, d)

        print("ADDED DEFINITION : ", name)
        print(f"INFO TYPE : {d.info.type}")
        print(f"VALUE : {d.value}")
        print(f"INFERRED TYPE : {infered_type}")

    
    @typechecked
    def add_theorem(self, name : Name, t : Theorem):
        print("ADDING THEOREM : ", name)
        self.check_declaration_info(t.info)

        infered_type = self.infer(t.value, clone=True)
        clone_t_info_type = clone_expression(t.info.type, use_same_fvars=True)
        if not self.def_eq(infered_type, clone_t_info_type, clone=False):
            raise DeclarationError(f"Theorem {name} has type {t.info.type} but inferred type {infered_type}")
        self.environment.add_declaration(name, t)

        print("ADDED THEOREM : ", name)
    
    def add_opaque(self, name : Name, o : Opaque):
        print("ADDING OPAQUE : ", name)
        self.check_declaration_info(o.info)

        inferred_type = self.infer(o.value, clone=True)
        clone_o_info_type = clone_expression(o.info.type, use_same_fvars=True)
        if not self.def_eq(inferred_type, clone_o_info_type, clone=False):
            raise DeclarationError(f"Opaque {name} has type {o.info.type} but inferred type {inferred_type}")
        
        self.environment.add_declaration(name, o)

        print("ADDED OPAQUE : ", name)

    def add_axiom(self, name : Name, a : Axiom):
        print("ADDING AXIOM : ", name)
        self.check_declaration_info(a.info)
        self.environment.add_declaration(name, a)

        print("ADDED AXIOM : ", name)
    
    def add_inductive(self, name : Name, ind : InductiveType):
        print("ADDING INDUCTIVE : ", name)
        self.check_declaration_info(ind.info)
        self.environment.add_declaration(name, ind)

        print("ADDED INDUCTIVE : ", name)

    def add_constructor(self, name : Name, constructor : Constructor):
        print("ADDING CONSTRUCTOR: ", name)
        self.check_declaration_info(constructor.info)

        inductive_def = self.environment.get_declaration_under_name(constructor.inductive_name)
        if not isinstance(inductive_def, InductiveType):
            raise DeclarationError(f"Constructor {name} is not associated with an inductive type.")
        if inductive_def.num_params != constructor.num_params:
            raise DeclarationError(f"Constructor {name} has {constructor.num_params} parameters but the inductive type {constructor.inductive_name} has {inductive_def.num_params} parameters.")
        


        self.environment.add_declaration(name, constructor)

        print("ADDED CONSTRUCTOR : ", name)

    def add_recursor(self, name : Name, recursor : Recursor):
        print("ADDING RECURSOR : ", name)
        self.check_declaration_info(recursor.info)

        for rec_rule in recursor.recursion_rules:
            print("ADDING RECURSOR RULE : ", rec_rule)
            #self.infer(rec_rule.value, clone=True)

            constructor_decl = self.environment.get_declaration_under_name(rec_rule.constructor)
            if not isinstance(constructor_decl, Constructor):
                raise DeclarationError(f"Recursor rule {rec_rule} is not associated with a constructor; found {constructor_decl.__class__.__name__} with name {constructor_decl.info.name} instead.")
            
            if constructor_decl.num_params != recursor.num_params:
                raise DeclarationError(f"Recursor rule {rec_rule} is associated with constructor {constructor_decl.info.name} which has {constructor_decl.num_params} parameters, but the recursor {recursor.info.name} has {recursor.num_params} parameters.")

        self.environment.add_declaration(name, recursor)

        print("ADDED RECURSOR : ", name)

    # adding declarations
    def add_declaration(self, name : Name, decl : Declaration):
        if isinstance(decl, Definition): self.add_definition(name, decl)
        elif isinstance(decl, Theorem): self.add_theorem(name, decl)
        elif isinstance(decl, Opaque): self.add_opaque(name, decl)
        elif isinstance(decl, Axiom): self.add_axiom(name, decl)
        elif isinstance(decl, InductiveType): self.add_inductive(name, decl)
        elif isinstance(decl, Constructor): self.add_constructor(name, decl)
        elif isinstance(decl, Recursor): self.add_recursor(name, decl)
        else: raise ValueError(f"Unknown declaration type {decl.__class__.__name__}")