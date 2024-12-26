from typing import List, Optional, Tuple

from typeguard import typechecked
from Structures.Environment.Declaration import Axiom, Constructor, Declaration, DeclarationInfo, Definition, InductiveType, Opaque, Recursor, Theorem
from Structures.Environment.Environment import Environment
from Structures.Environment.LocalContext import LocalContext
from Structures.Expression.Expression import *
from Structures.Expression.ExpressionManipulation import abstract_bvar, clone_expression, fold_apps, instantiate_bvar, has_fvars, unfold_apps
from Structures.Expression.Level import *
from Structures.Expression.LevelManipulation import antisymm_eq, antisymm_eq_list, are_unique_level_params, clone_level
from Structures.KernelErrors import ExpectedDifferentExpressionError, ExpectedDifferentTypesError, PanicError, ProjectionError, EnvironmentError, DeclarationError
from Structures.Name import Name

#TODO s:
# - special cases for Nat and String literals
# - quot

class TypeChecker:
    def __init__(self):
        self.environment = Environment()
        self.local_context = LocalContext()

    def check_declar_info(self, info: DeclarationInfo):
        if not are_unique_level_params(info.lvl_params):
            raise EnvironmentError(f"Level parameters in declaration info {info} are not unique.")
        if has_fvars(info.type):
            raise EnvironmentError(f"Type in declaration info {info} contains free variables.")
        
        inferred_type = self.infer_core(info.type, clone=True)
        self.ensure_sort(inferred_type)

    def ensure_sort(self, e: Expression) -> Level:
        if isinstance(e, Sort):
            return e.level
        # TODO: is reduction ok here?
        #whnfd_expr = self.whnf(e)
        #if isinstance(whnfd_expr, Sort):
        #    return whnfd_expr.level
        raise PanicError("ensure_sort could not produce a sort")

    def create_fvar(self, name: Name, expr: Expression, val : Optional[Expression]) -> FVar:
        fvar = FVar(name)
        self.local_context.add_fvar(fvar, expr, val)
        return fvar

    def remove_fvar(self, fvar: FVar):
        self.local_context.remove_fvar(fvar)
    
    def get_type_of_fvar(self, fvar : FVar) -> Expression:
        return self.local_context.get_fvar_type(fvar, use_same_fvars=True)
    
    def get_value_of_fvar(self, fvar : FVar) -> Optional[Expression]:
        return self.local_context.get_fvar_value(fvar, use_same_fvars=True)
    
    def instantiate(self, bname : Name, arg_type : Expression, body : Expression, clone : bool, use_same_fvars : bool, val : Optional[Expression] = None) -> Tuple[FVar, Expression]:
        fvar = self.create_fvar(bname, arg_type, val)
        return fvar, instantiate_bvar(body, fvar, clone=clone, use_same_fvars=use_same_fvars)
    
    def instantiate_multiple_bodies(self, bnames : Name, arg_types : Expression, bodies : List[Expression], clone : bool, use_same_fvars : bool, val : Optional[Expression] = None) -> Tuple[FVar, List[Expression]]:
        fvar = self.create_fvar(bnames, arg_types, val)
        return fvar, [instantiate_bvar(body, fvar, clone=clone, use_same_fvars=use_same_fvars) for body in bodies]
    
    def abstract(self, fvar: FVar, expr : Expression, clone : bool, use_same_fvars : bool) -> Expression:
        """Abstracts the outermost bound variable in the given expression."""
        # remove the fvar from the local context
        self.remove_fvar(fvar)
        return abstract_bvar(expr, fvar, clone=clone, use_same_fvars=use_same_fvars)

    # DEFINITIONAL EQUALITY
    def def_eq_sort(self, l: Sort, r: Sort) -> bool:
        """Sorts are equal if their levels satisfy antisymmetry.
        The comparsion function does not change anything, so def_eq_sort is safe to use when passing by reference.
        """
        return antisymm_eq(l.level, r.level)

    def def_eq_const(self, l: Const, r: Const) -> bool:
        """
        If the names are the same, and the level parameters are equal, then the constants are equal.
        Since nothing is changed, this function is safe to use when passing by reference.
        """
        return l.name == r.name and antisymm_eq_list(l.lvl_params, r.lvl_params)

    def def_eq_bvar(self, l: BVar, r: BVar) -> bool:
        raise PanicError("BVar should have been substituted by now, when comparing expressions for definitional equality.")

    def def_eq_fvar(self, l: FVar, r: FVar) -> bool:
        """
        For FVars, we are using the is operator to compare them. 
        They are only a place holder for the actual type, so this is enough. However, care must be taken when cloning.
        """
        return l is r

    def def_eq_app(self, l: App, r: App, clone : bool) -> bool:
        return self.def_eq(l.fn, r.fn, clone=clone) and self.def_eq(l.arg, r.arg, clone=clone)

    def def_eq_pi(self, l: Pi, r: Pi, clone : bool) -> bool:
        if not self.def_eq(l.arg_type, r.arg_type, clone=clone):
            return False
        
        fvar, (n_l, n_r) = self.instantiate_multiple_bodies(l.bname, l.arg_type, [l.body_type, r.body_type], clone=clone, use_same_fvars=True)
        
        ret = self.def_eq(n_l, n_r, clone=False) # n_l and n_r are already separated from l and r when instantiated, so def_eq can do whatever it wants
        self.remove_fvar(fvar)
        return ret

    def def_eq_lambda(self, l: Lambda, r: Lambda, clone : bool) -> bool:
        if not self.def_eq(l.arg_type, r.arg_type, clone=clone):
            return False
        
        fvar, (n_l, n_r) = self.instantiate_multiple_bodies(l.bname, l.arg_type, [l.body, r.body], clone=clone, use_same_fvars=True)
        ret = self.def_eq(n_l, n_r, clone=False) # n_l and n_r are already separated from l and r when instantiated, so def_eq can do whatever it wants
        self.remove_fvar(fvar)
        return ret
    
    @typechecked
    def is_structural_inductive(self, inductive : InductiveType) -> bool:
        return inductive.number_of_constructors() == 1
    
    def is_structural_constructor(self, constructor : Constructor) -> Optional[InductiveType]:
        inductive_type_name = constructor.inductive_name
        inductive_decl = self.environment.get_inductive(inductive_type_name)
        if self.is_structural_inductive(inductive_decl):
            return inductive_decl
        return None

    def try_structural_eta_expansion_core(self, t : Expression, s : Expression) -> bool:
        s_fn, s_args = unfold_apps(s)

        if not isinstance(s_fn, Const):
            return False
        
        decl = self.environment.get_declaration_under_name(s_fn.name)

        if not isinstance(decl, Constructor): return False
        if len(s_args) != decl.num_params + decl.num_fields: return False

        inductive_decl = self.is_structural_constructor(decl)
        if inductive_decl is None: return False
        if not self.def_eq(self.infer_core(t, clone=False), self.infer_core(s, clone=False), clone=False): return False

        for i in range(decl.num_params, len(s_args)):
            proj = Proj(type_name=inductive_decl.info.name, index=i-decl.num_params, struct=t)
            if not self.def_eq(proj, s_args[i], clone=False): return False

        return True

    def try_structural_eta_expansion(self, l : Expression, r : Expression) -> bool:
        return self.try_structural_eta_expansion_core(l, r) or self.try_structural_eta_expansion_core(r, l)
    
    def try_eta_expansion_core(self, t : Expression, s : Expression) -> bool:
        """
        Tries to eta expand s: if s is a function, then by eta expansion, it is equal to the expression "fun x => s x".
        Always assumes that t and s we cloned beforehand.
        """
        if not (isinstance(t, Lambda) and not isinstance(s, Lambda)):
            return False
        s_type = self.whnf(self.infer_core(s, clone=False), clone=False)
        if not isinstance(s_type, Pi):
            return False
        new_s = Lambda(bname=s_type.bname, arg_type=s_type.arg_type, body=App(s, BVar(0)))
        return self.def_eq(t, new_s, clone=False)

    def try_eta_expansion(self, x : Expression, y : Expression) -> bool:
        """
        Tries to eta expand y and compares it to x, then tries to eta expand x and compares it to y.
        Always assumes that x and y were cloned beforehand.
        """
        return self.try_eta_expansion_core(x, y) or self.try_eta_expansion_core(y, x)

    def def_eq(self, l: Expression, r: Expression, clone : bool) -> bool:
        if l is r:
            return True
        
        l_n = self.whnf(l, clone=clone)
        r_n = self.whnf(r, clone=clone)


        # cannot be reduced further
        if isinstance(l_n, Sort) and isinstance(r_n, Sort):
            return self.def_eq_sort(l_n, r_n)
        elif isinstance(l_n, Const) and isinstance(r_n, Const):
            return self.def_eq_const(l_n, r_n)
        elif isinstance(l_n, BVar) and isinstance(r_n, BVar):
            return self.def_eq_bvar(l_n, r_n)
        elif isinstance(l_n, FVar) and isinstance(r_n, FVar):
            return self.def_eq_fvar(l_n, r_n)
        
        elif isinstance(l_n, App) and isinstance(r_n, App):
            if self.def_eq_app(l_n, r_n, clone=False):
                return True
        elif isinstance(l_n, Pi) and isinstance(r_n, Pi):
            if self.def_eq_pi(l_n, r_n, clone=False):
                return True
        elif isinstance(l_n, Lambda) and isinstance(r_n, Lambda):
            if self.def_eq_lambda(l_n, r_n, clone=False):
                return True
        # TODO: reductions

        if self.try_structural_eta_expansion(l_n, r_n): # l_n and r_n are already whnfed and so cloned, therefore, try_eta_expansion can do whatever it wants
            return True
        # TODO: should try_eta_expansion get the cloned expressions of l_n and r_n before we tried structural eta expansion?
        if self.try_eta_expansion(l_n, r_n): # l_n and r_n are already whnfed and so cloned, therefore, try_eta_expansion can do whatever it wants
            return True

        return False
    
    # REDUCTION
    def beta_reduction(self, expr : App, clone : bool) -> Expression:
        f, args = unfold_apps(expr.fn)
        for arg in args:
            if isinstance(f, Lambda):
                _, f = self.instantiate(f.bname, arg, f.body, clone=clone, use_same_fvars=True)
            else:
                break

        return fold_apps(f, args)

    def zeta_reduction(self, expr : Let, clone : bool) -> Expression:
        """
        Reduces the let expression by substituting the value in the body.
        """
        _, sub_expr = self.instantiate(expr.bname, expr.val, expr.body, clone=clone, val=expr.val, use_same_fvars=True)
        return sub_expr

    def unfold_definition(self, c : Const) -> Expression:
        decl = self.environment.get_declaration_under_name(c.name)
        if isinstance(decl, Definition) or isinstance(decl, Theorem):
            return self.environment.get_cloned_val_with_substituted_level_params(decl, c.lvl_params)
        else:
            return c # nothing can be done

    def delta_reduction(self, expr : Const) -> Expression:
        # unfold definition but also unfold definition
        fn, args = unfold_apps(self.unfold_definition(expr))
        if isinstance(fn, Const):
            unfolded_fn = self.delta_reduction(fn)
            return fold_apps(unfolded_fn, args)
        return expr # nothing can be done

    def proj_reduction(self, proj : Proj, clone : bool) -> Optional[Expression]:
        pos_cons = self.proj_get_constructor(proj, clone=clone)
        if pos_cons is None:
            return None
        _, constructor, args = pos_cons

        num_params = constructor.num_params
        if proj.index + num_params >= len(args):
            return None
        return args[proj.index + num_params]
    
    def fvar_reduction(self, fvar : FVar) -> Expression:
        pos_val = self.get_value_of_fvar(fvar)
        if pos_val is None:
            raise PanicError(f"FVar {fvar} does not have a value.")
        return fvar
    
    def reduce_recursor(self, e : Expression) -> Optional[Expression]:
        raise NotImplementedError("Recursor reduction not implemented yet.")
        # TODO: quotient
        #if (env().is_quot_initialized()) {
        #    if (optional<expr> r = quot_reduce_rec(e, [&](expr const & e) { return whnf(e); })) {
        #        return r;
        #    }
        #}
        fn, args = unfold_apps(e)
        if not isinstance(fn, Const): return None
        
        rec_decl = self.environment.get_declaration_under_name(fn.name)
        if not isinstance(rec_decl, Recursor): return None

        rec_val = rec_decl


        #recursor_val const & rec_val = rec_info->to_recursor_val();
        #unsigned major_idx           = rec_val.get_major_idx();
        #if (major_idx >= rec_args.size()) return none_expr(); // major premise is missing
        #expr major     = rec_args[major_idx];
        #if (rec_val.is_k()) {
        #    major = to_cnstr_when_K(env, rec_val, major, whnf, infer_type, is_def_eq);
        #}
        #major = whnf(major);
        #if (is_nat_lit(major))
        #    major = nat_lit_to_constructor(major);
        #else if (is_string_lit(major))
        #    major = string_lit_to_constructor(major);
        #else
        #    major = to_cnstr_when_structure(env, rec_val.get_major_induct(), major, whnf, infer_type);
        #optional<recursor_rule> rule = get_rec_rule_for(rec_val, major);
        #if (!rule) return none_expr();
        #buffer<expr> major_args;
        #get_app_args(major, major_args);
        #if (rule->get_nfields() > major_args.size()) return none_expr();
        #if (length(const_levels(rec_fn)) != length(rec_info->get_lparams())) return none_expr();
        #expr rhs = instantiate_lparams(rule->get_rhs(), rec_info->get_lparams(), const_levels(rec_fn));
        #/* apply parameters, motives and minor premises from recursor application. */
        #rhs      = mk_app(rhs, rec_val.get_nparams() + rec_val.get_nmotives() + rec_val.get_nminors(), rec_args.data());
        #/* The number of parameters in the constructor is not necessarily
        #equal to the number of parameters in the recursor when we have
        #nested inductive types. */
        #unsigned nparams = major_args.size() - rule->get_nfields();
        #/* apply fields from major premise */
        #rhs      = mk_app(rhs, rule->get_nfields(), major_args.data() + nparams);
        #if (rec_args.size() > major_idx + 1) {
        #    /* recursor application has more arguments after major premise */
        #    unsigned nextra = rec_args.size() - major_idx - 1;
        #    rhs = mk_app(rhs, nextra, rec_args.data() + major_idx + 1);
        #}
        #return some_expr(rhs);
        #return none_expr();
            

    def whnf(self, expr : Expression, clone : bool) -> Expression:
        if clone:
            expr = clone_expression(expr, use_same_fvars=True)

        if isinstance(expr, BVar) or isinstance(expr, Sort) or isinstance(expr, Pi) or isinstance(expr, Const) or isinstance(expr, NatLit) or isinstance(expr, StringLit): return expr
        if isinstance(expr, FVar):
            if not isinstance(self.get_type_of_fvar(expr), Let):
                return expr
        
        # TODO: caching
        r = None   
        if isinstance(expr, FVar):
            r = self.fvar_reduction(expr) # this always clones the value of the fvar from the context
        elif isinstance(expr, Proj):
            pos_red = self.proj_reduction(expr, clone=False) 
            if pos_red is None:
                r = expr
            else:
                r = self.whnf(pos_red, clone=False)     
        elif isinstance(expr, App):
            fn, _ = unfold_apps(expr)
            if isinstance(fn, Lambda):
                r = self.whnf(self.beta_reduction(expr, clone=False), clone=False)
            elif isinstance(fn, Const):
                raise NotImplementedError("Delta reduction not implemented yet.")
                r = self.reduce_recursor(expr)
                if r is not None:
                    return self.whnf(r, clone=False)
                else:
                    return expr
            else:
                r = expr
        elif isinstance(expr, Let):
            r = self.whnf(self.zeta_reduction(expr, clone=False), clone=False)
        
        if r is None:
            raise PanicError(f"Expr of type {expr.__class__.__name__} could not be mathed, this should not happen.")

        return r

    # TYPE INFERENCE
    def infer_fvar(self, fvar : FVar):
        return self.get_type_of_fvar(fvar)
        
    def infer_app(self, app : App, clone : bool) -> Expression:
        whnfd_fn_type = self.whnf(self.infer_core(app.fn, clone=clone), clone=False)
        if isinstance(whnfd_fn_type, Pi):
            inferred_arg_type = self.infer_core(app.arg, clone=clone)
            if not self.def_eq(whnfd_fn_type.arg_type, inferred_arg_type, clone=False):
                raise ExpectedDifferentTypesError(whnfd_fn_type.arg_type, inferred_arg_type)
            fvar, infered_type = self.instantiate(whnfd_fn_type.bname, app.arg, whnfd_fn_type.body_type, clone=False, use_same_fvars=True)
            self.remove_fvar(fvar)
            return infered_type
            
        raise ExpectedDifferentExpressionError(Pi, whnfd_fn_type.__class__)

    def infer_sort(self, sort : Sort, clone : bool) -> Expression:
        if clone:
            return Sort(LevelSucc(clone_level(sort.level)))
        return Sort(LevelSucc(sort.level))

    def infer_pi(self, pi : Pi, clone : bool) -> Expression:
        lhs = self.infer_sort_of(pi.arg_type, clone=clone)

        fvar, inst_body_type = self.instantiate(pi.bname, pi.arg_type, pi.body_type, clone=clone, use_same_fvars=True)
        rhs = self.infer_sort_of(inst_body_type, clone=False)
        self.remove_fvar(fvar)

        return Sort(LevelIMax(lhs, rhs))
    
    def infer_sort_of(self, e : Expression, clone : bool) -> Level:
        whnf_d_e_type = self.whnf(self.infer_core(e, clone=clone), clone=False)
        if isinstance(whnf_d_e_type, Sort):
            return whnf_d_e_type.level
        raise ExpectedDifferentExpressionError(Sort, whnf_d_e_type.__class__)
    
    def infer_lambda(self, e : Lambda, clone : bool) -> Expression:
        self.infer_sort_of(e.arg_type, clone=clone)
        bname = e.bname
        fvar, inst_body = self.instantiate(bname, e.arg_type, e.body, clone=clone, use_same_fvars=True)
        infered_body_type = self.infer_core(inst_body, clone=False)
        infered_pi = Pi(bname, e.arg_type, self.abstract(fvar, infered_body_type, clone=False, use_same_fvars=True))

        return infered_pi
    
    def infer_const(self, c : Const) -> Expression:
        # this always clones the type from the environment
        return self.environment.get_constant_type(c)
    
    def infer_let(self, e : Let, clone : bool) -> Expression:
        self.infer_sort_of(e.arg_type, clone=clone)
        inferred_val_type = self.infer_core(e.val, clone=clone)
        if not self.def_eq(inferred_val_type, e.arg_type, clone=False):
            raise ExpectedDifferentTypesError(inferred_val_type, e.arg_type)
        
        fvar, inst_body = self.instantiate(e.bname, e.arg_type, e.body, clone=clone, val=e.val, use_same_fvars=True)
        inferred_type = self.infer_core(inst_body, clone=False)
        self.remove_fvar(fvar)
        return inferred_type
    
    def proj_get_constructor(self, proj : Proj, clone : bool) -> Optional[Tuple[Const, Constructor, List[Expression]]]:
        """Returns the inductive type constant, the corresponding constructor, and the arguments to the constructor."""
        struct_type = self.whnf(self.infer_core(proj.struct, clone=clone), clone=False)
        inductive_mk, args = unfold_apps(struct_type)
        if not isinstance(inductive_mk, Const):
            return None
        
        inductive_decl = self.environment.get_inductive(inductive_mk.name)
        if inductive_decl.number_of_constructors() != 1:
            return None
        
        constructor = self.environment.get_constructor(inductive_mk.name)
        return inductive_mk, constructor, args

    def infer_proj(self, proj : Proj, clone : bool) -> Expression:
        pos_cons = self.proj_get_constructor(proj, clone=clone)
        if pos_cons is None:
            raise ProjectionError(f"Could not get constructor for projection {proj}")
        inductive_mk, constructor, args = pos_cons
        constructor_type = self.environment.get_cloned_type_with_substituted_level_params(constructor, inductive_mk.lvl_params)
        
        for i in range(constructor.num_params):
            constructor_type = self.whnf(constructor_type, clone=False)
            if not isinstance(constructor_type, Pi):
                raise ProjectionError(f"Expected a Pi type for parameter when reducing constructor type but got {constructor_type.__class__}")
            if i >= len(args):
                raise ProjectionError(f"Ran out of arguments for parameters when reducing constructor type.")
            
            fvar, constructor_type = self.instantiate(constructor_type.bname, args[i], constructor_type.body_type, clone=False, use_same_fvars=True)
            if not isinstance(constructor_type, Pi):
                raise PanicError(f"When substituting parameter {i} in constructor type, Pi type was somehow lost.")
            self.remove_fvar(fvar)

        for i in range(proj.index):
            constructor_type = self.whnf(constructor_type, clone=False)
            if not isinstance(constructor_type, Pi):
                raise ProjectionError(f"Expected a Pi type for index when reducing constructor type but got {constructor_type.__class__}")

            fvar, constructor_type = self.instantiate(constructor_type.bname, Proj(inductive_mk.name, i, proj.struct), constructor_type.body_type, clone=False, use_same_fvars=True)
            if not isinstance(constructor_type, Pi):
                raise PanicError(f"When substituting index {i} in constructor type, Pi type was somehow lost.")
            self.remove_fvar(fvar)
        
        constructor_type = self.whnf(constructor_type, clone=False)
        if not isinstance(constructor_type, Pi):
            raise ProjectionError(f"Expected a Pi type for projection index but got {constructor_type.__class__}")
        
        return constructor_type.arg_type

    def infer_nat_lit(self, n : NatLit) -> Expression:
        return Const(self.environment.get_nat_name(), [])
    
    def infer_string_lit(self, s : StringLit) -> Expression:
        return Const(self.environment.get_string_name(), [])

    def infer_core(self, expr : Expression, clone : bool) -> Expression:
        """
        If check is true, we perform definitional equality checks (for example, the type of an
        argument to a lambda is the same type as the binder in the labmda). These checks
        are costly however, and in some cases we're using inference during reduction of
        expressions we know to be well-typed, so we can pass the flag `InferOnly` to omit
        these checks when they are not needed. (TODO change this comment)
        """
        if isinstance(expr, BVar): raise PanicError("BVar should have been substituted when inferring")
        elif isinstance(expr, FVar): return self.infer_fvar(expr) # we should not clone the fvar since we are using "is" to compare
        elif isinstance(expr, App): return self.infer_app(expr, clone=clone)
        elif isinstance(expr, Sort): return self.infer_sort(expr, clone=clone)
        elif isinstance(expr, Const): return self.infer_const(expr) # const always copies the type of the const from the environment
        elif isinstance(expr, Lambda): return self.infer_lambda(expr, clone=clone)
        elif isinstance(expr, Pi): return self.infer_pi(expr, clone=clone)
        elif isinstance(expr, Let): return self.infer_let(expr, clone=clone)
        elif isinstance(expr, Proj): return self.infer_proj(expr, clone=clone)
        elif isinstance(expr, NatLit): return self.infer_nat_lit(expr) # this always returns a new const
        elif isinstance(expr, StringLit): return self.infer_string_lit(expr) # this always returns a new const
        else: raise ValueError(f"Unknown expression type {expr.__class__.__name__}")

    def infer(self, expr : Expression, clone : bool) -> Expression:
        if not self.local_context.is_empty():
            raise PanicError("Local context is not empty when inferring.")
        inferred_type = self.infer_core(expr, clone=clone)
        self.local_context.clear()
        return inferred_type

    # CHECKING DECLARATIONS
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
        self.check_declaration_info(d.info)

        infered_type = self.infer(d.value, clone=True)
        clone_d_info_type = clone_expression(d.info.type, use_same_fvars=True)
        if not self.def_eq(infered_type, clone_d_info_type, clone=False):
            raise DeclarationError(f"Definition {name} has type {d.info.type} but inferred type {infered_type}")
        self.environment.add_declaration(name, d)
    
    @typechecked
    def add_theorem(self, name : Name, t : Theorem):
        self.check_declaration_info(t.info)

        infered_type = self.infer(t.value, clone=True)
        clone_t_info_type = clone_expression(t.info.type, use_same_fvars=True)
        if not self.def_eq(infered_type, clone_t_info_type, clone=False):
            raise DeclarationError(f"Theorem {name} has type {t.info.type} but inferred type {infered_type}")
        self.environment.add_declaration(name, t)
    
    def add_opaque(self, name : Name, o : Opaque):
        self.check_declaration_info(o.info)

        inferred_type = self.infer(o.value, clone=True)
        clone_o_info_type = clone_expression(o.info.type, use_same_fvars=True)
        if not self.def_eq(inferred_type, clone_o_info_type, clone=False):
            raise DeclarationError(f"Opaque {name} has type {o.info.type} but inferred type {inferred_type}")
        
        self.environment.add_declaration(name, o)

    def add_axiom(self, name : Name, a : Axiom):
        self.check_declaration_info(a.info)
        self.environment.add_declaration(name, a)
    
    def add_inductive(self, name : Name, ind : InductiveType):
        self.check_declaration_info(ind.info)
        self.environment.add_declaration(name, ind)

    def add_constructor(self, name : Name, constructor : Constructor):
        self.check_declaration_info(constructor.info)
        self.environment.add_declaration(name, constructor)

    def add_recursor(self, name : Name, recursor : Recursor):
        print("Adding recursor")
        print(recursor)
        self.check_declaration_info(recursor.info)
        self.environment.add_declaration(name, recursor)

    
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