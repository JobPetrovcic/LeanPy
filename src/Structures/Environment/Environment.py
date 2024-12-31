from typing import Dict, List

from typeguard import typechecked

from Structures.Environment.Declaration import Constructor, Declaration, Definition, InductiveType, Opaque, Quot, Theorem
from Structures.Expression.Expression import Const, Expression, Sort
from Structures.Expression.ExpressionManipulation import substitute_level_params_in_expression
from Structures.Expression.Level import Level, LevelSucc, LevelZero
from Structures.Name import Anonymous, Name, SubName

class Environment:
    def __init__(self):
        self.checking_inductive = False
        self.init_name_dict()
    
    def get_anonymous(self) -> Anonymous:
        return self.anonymous

    def init_name_dict(self):
        self.init_bases()
        self.name_dict : Dict[Name, Declaration ] = {}
    
    # SPECIAL STRUCTURES : Nat, String, Quot (TODO : List)

    def create_name_from_str(self, name_str : str) -> Name:
        """ Creates a name from a string. """
        parts = name_str.split(".")
        cur = self.anonymous
        for part in parts:
            cur = SubName(cur, part)
        return cur

    def init_bases(self):
        self.anonymous = Anonymous()
        self.level_zero = LevelZero()
        self.level_one = LevelSucc(self.level_zero)
        self.Prop = Sort(self.level_zero)
        self.Type = Sort(self.level_one)

        # Nat constants
        self.Nat_name = self.create_name_from_str("Nat")
        self.Nat_zero_name = SubName(self.Nat_name, "zero")
        self.Nat_succ_name = SubName(self.Nat_name, "succ")
        self.Nat_add_name = SubName(self.Nat_name, "add")
        self.Nat_sub_name = SubName(self.Nat_name, "sub")
        self.Nat_mul_name = SubName(self.Nat_name, "mul")
        self.Nat_pow_name = SubName(self.Nat_name, "pow")
        self.Nat_gcd_name = SubName(self.Nat_name, "gcd")
        self.Nat_div_name = SubName(self.Nat_name, "div")
        self.Nat_mod_name = SubName(self.Nat_name, "mod")
        self.Nat_beq_name = SubName(self.Nat_name, "beq")
        self.Nat_ble_name = SubName(self.Nat_name, "ble")
        self.Nat_land_name = SubName(self.Nat_name, "land")
        self.Nat_lor_name = SubName(self.Nat_name, "lor")
        self.Nat_xor_name = SubName(self.Nat_name, "xor")
        self.Nat_shiftLeft_name = SubName(self.Nat_name, "shiftLeft")
        self.Nat_shiftRight_name = SubName(self.Nat_name, "shiftRight")

        # String constants
        self.String_name = self.create_name_from_str("String")
        self.String_mk_name = SubName(self.String_name, "mk")
        
        # List constants
        self.List_name = self.create_name_from_str("List")
        self.List_nil_name = SubName(self.List_name, "nil")
        self.List_cons_name = SubName(self.List_name, "cons")
        self.Char_name = self.create_name_from_str("Char")

        # Quot constants
        self.Quot_name = self.create_name_from_str("Quot")
        self.Quot_mk_name = SubName(self.Quot_name, "mk")
        self.Quot_lift_name = SubName(self.Quot_name, "lift")
        self.Quot_ind_name = SubName(self.Quot_name, "ind")
                                        

    @typechecked
    def get_declaration_under_name(self, name : Name) -> Declaration:
        if name not in self.name_dict:
            print([str(k) for k in self.name_dict.keys()])
            raise ValueError(f"Name {name} does not exist in environment.")
        found = self.name_dict[name]
        if not self.checking_inductive:
            if isinstance(found, InductiveType):
                if not found.is_checked:
                    raise ValueError(f"Inductive type {name} has not been checked.")
            elif isinstance(found, Constructor):
                if not found.is_checked:
                    raise ValueError(f"Constructor {name} has not been checked.")
        
        return found
    
    def exists_declaration_under_name(self, name : Name) -> bool:
        return name in self.name_dict
    
    @typechecked
    def get_declaration_type_with_substituted_level_params(self, decl : Declaration, subs : List[Level]) -> Expression:
        if len(decl.info.lvl_params) != len(subs):
            print(f"decl parameters : {[str(l) for l in decl.info.lvl_params]}")
            print(f"subs parameters : {[str(l) for l in subs]}")
            raise ValueError(f"Declaration {decl.info.name} has {len(decl.info.lvl_params)} level parameters, but {len(subs)} substitutions were provided.")
        substitutions = list(zip(decl.info.lvl_params, subs))
        return substitute_level_params_in_expression(decl.get_type(), substitutions) # this clones the expression
    
    @typechecked
    def get_declaration_val_with_substituted_level_params(self, decl : Definition | Theorem | Opaque, subs : List[Level]) -> Expression:
        if len(decl.info.lvl_params) != len(subs):
            raise ValueError(f"Declaration {decl} has a different number of level parameters than the substitutions provided.")
        substitutions = list(zip(decl.info.lvl_params, subs))
        return substitute_level_params_in_expression(decl.value, substitutions) # this clones the expression
    
    @typechecked
    def get_constant_type(self, c : Const) -> Expression:
        decl = self.get_declaration_under_name(c.name)
        
        sub_constant_type = self.get_declaration_type_with_substituted_level_params(decl, c.lvl_params)

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
