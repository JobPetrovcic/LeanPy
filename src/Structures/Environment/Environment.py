from typing import Dict, List

from typeguard import typechecked

from Structures.Environment.Declaration import Constructor, Declaration, DeclarationInfo, Definition, InductiveType, Opaque, Quot, Theorem
from Structures.Environment.ExpressionConstruction import create_arrow_type, create_named_fvar, create_sort_param
from Structures.Expression.Expression import App, Const, Expression, FVar, Pi, Sort
from Structures.Expression.ExpressionManipulation import fold_apps, substitute_level_params_in_expression
from Structures.Expression.Level import Level, LevelParam, LevelSucc, LevelZero
from Structures.Name import Anonymous, Name, SubName

class Environment:
    def __init__(self):
        
        self.init_name_dict()
    
    def get_anonymous(self) -> Anonymous:
        return self.anonymous

    def init_name_dict(self):
        self.init_bases()
        self.name_dict : Dict[Name, Declaration | None] = {Anonymous() : None}
        self.init_special_structures()
    
    # SPECIAL STRUCTURES : Nat, String, Quot (TODO : List)

    def init_bases(self):
        self.anonymous = Anonymous()
        self.level_zero = LevelZero()
        self.level_one = LevelSucc(self.level_zero)
        self.Prop = Sort(self.level_zero)
        self.Type = Sort(self.level_one)
    
    def init_natural_numbers(self):
        self.NatName = SubName(self.get_anonymous(), "Nat")
        self._add_subname(self.NatName, None)

    def init_string(self):
        self.StringName = SubName(self.get_anonymous(), "String")
        self._add_subname(self.StringName, None)
    
    def init_quotient(self):
        """
        for quotient we have the following declarations:
         - Quot.{u} {α : Sort u} (r : α → α → Prop) : Sort u
         - Quot.mk.{u} {α : Sort u} (r : α → α → Prop) (a : α) : Quot r
         - Quot.lift.{u, v} {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β) (a : ∀ (a b : α), r a b → f a = f b) : Quot r → β
         - Quot.ind.{u} {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop} (mk : ∀ (a : α), β (Quot.mk r a)) (q : Quot r) : β q
        """

        NotImplementedError("Quotient not implemented yet.")

        self.Quot_name = SubName(self.get_anonymous(), "Quot")
        self.Quot_mk_name = SubName(self.Quot_name, "mk")
        self.Quot_lift_name = SubName(self.Quot_name, "lift")
        self.Quot_ind_name = SubName(self.Quot_name, "ind")

        # define universe u
        param_u, sort_u = create_sort_param(self.Quot_name, "u")

        # define alpha 
        alpha = create_named_fvar(self.Quot_name, "α", sort_u)

        # define r : alpha -> alpha -> Prop
        r_type = create_arrow_type([(None, alpha[1]), (None, alpha[1])], self.Prop, self.Quot_name) # None will be replaced with an anonymous name

        r = create_named_fvar(self.Quot_name, "r", r_type)
        # define Quot.{u} {α : Sort u} (r : α → α → Prop) : Sort u
        Quot_type = create_arrow_type([alpha, r], sort_u, self.Quot_name)

        # add Quot to the environment
        Quot_info = DeclarationInfo(self.Quot_name, [param_u], Quot_type)
        Quot_def = Quot(Quot_info)
        self.add_quot_declaration(self.Quot_name, Quot_def)

        # define Quot.mk.{u} {α : Sort u} (r : α → α → Prop) (a : α) : Quot r
        a = create_named_fvar(self.Quot_name, "a", alpha[1])
        Quot_mk_type = create_arrow_type([alpha, r, a], fold_apps(Const(self.Quot_name, [param_u]), [alpha[1], r[1], a[1]]), self.Quot_name)


        Quot_mk_info = DeclarationInfo(self.Quot_mk_name, [param_u], Quot_mk_type)
        Quot_mk_def = Quot(Quot_mk_info)
        self.add_quot_declaration(self.Quot_mk_name, Quot_mk_def)

        b = create_named_fvar(self.Quot_name, "b", alpha[1])
        
        # define Quot.lift.{u, v} {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β) (f_a_eq_f_b : ∀ (a b : α), r a b → f a = f b) : Quot r → β
        param_v, sort_v = create_sort_param(self.Quot_name, "v")
        beta = create_named_fvar(self.Quot_name, "β", sort_v)

        f_type = create_arrow_type([(None, alpha[1])], beta[1], self.Quot_name)
        f = create_named_fvar(self.Quot_name, "f", f_type)

        f_a_eq_f_b_type = create_arrow_type([a, b, (None, fold_app(r[1], [a[1], b[1]]))],  )
        


        Qout_lift_type = create_arrow_type([alpha, r, beta, f, ])
                                        

    def init_special_structures(self):
        self.init_natural_numbers()
        self.init_string()
        #self.init_quotient()

    def get_nat_name(self) -> SubName:
        return self.NatName
    
    def get_string_name(self) -> SubName:
        return self.StringName
    
    @typechecked
    def _add_subname(self, name : SubName, decl : Declaration | None):
        if not name.ancestor in self.name_dict:
            raise ValueError(f"Ancestor {name.ancestor} not found in environment.")
        if name in self.name_dict:
            raise ValueError(f"Name {name} already exists in environment.")
        self.name_dict[name] = decl

    @typechecked
    def get_declaration_under_name(self, name : Name) -> Declaration:
        if name not in self.name_dict:
            raise ValueError(f"Name {name} not found in environment.")
        found = self.name_dict[name]
        if found is None:
            raise ValueError(f"Name {name} does not specify a declaration, it is an empty name.")
        return found
    
    def exists_declaration_under_name(self, name : Name) -> bool:
        return name in self.name_dict
    
    @typechecked
    def get_cloned_type_with_substituted_level_params(self, decl : Declaration, subs : List[Level]) -> Expression:
        if len(decl.info.lvl_params) != len(subs):
            print(f"decl parameters : {[str(l) for l in decl.info.lvl_params]}")
            print(f"subs parameters : {[str(l) for l in subs]}")
            raise ValueError(f"Declaration {decl} has {len(decl.info.lvl_params)} level parameters, but {len(subs)} substitutions were provided.")
        substitutions = list(zip(decl.info.lvl_params, subs))
        return substitute_level_params_in_expression(decl.get_type(), substitutions) # this clones the expression
    
    @typechecked
    def get_cloned_val_with_substituted_level_params(self, decl : Definition | Theorem | Opaque, subs : List[Level]) -> Expression:
        if len(decl.info.lvl_params) != len(subs):
            raise ValueError(f"Declaration {decl} has a different number of level parameters than the substitutions provided.")
        substitutions = list(zip(decl.info.lvl_params, subs))
        return substitute_level_params_in_expression(decl.value, substitutions) # this clones the expression
    
    @typechecked
    def get_constant_type(self, c : Const) -> Expression:
        decl = self.get_declaration_under_name(c.name)
        
        sub_constant_type = self.get_cloned_type_with_substituted_level_params(decl, c.lvl_params)

        return sub_constant_type

    @typechecked
    def get_inductive(self, name : Name) -> InductiveType:
        decl = self.get_declaration_under_name(name)
        if not isinstance(decl, InductiveType):
            raise ValueError(f"Name {name} is not an inductive type.")
        return decl

    @typechecked
    def get_constructor(self, name : Name) -> Constructor:
        decl = self.get_declaration_under_name(name)
        if not isinstance(decl, Constructor):
            raise ValueError(f"Name {name} is not a constructor.")
        return decl
    
    @typechecked
    def add_declaration(self, name : Name, decl : Declaration):
        if name in self.name_dict:
            raise ValueError(f"Name {name} already exists in environment.")
        self.name_dict[name] = decl
    
    @typechecked
    def add_quot_declaration(self, name : Name, decl : Quot):
        if name in self.name_dict:
            raise ValueError(f"Name {name} already exists in environment.")
        self.name_dict[name] = decl
