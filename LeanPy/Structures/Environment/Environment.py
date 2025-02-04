from typing import Dict
from LeanPy.Structures.Environment.Declarations.Declaration import Constructor, Declaration, Inductive
from LeanPy.Structures.Name import *
from LeanPy.Structures.Expression.Level import *
from LeanPy.Structures.Expression.Expression import *
from LeanPy.Structures.Name import string_to_name

class Environment:
    def __init__(self):
        self.checking_inductive = False
        self.init_name_dict()
    
    def get_anonymous(self) -> Anonymous:
        return self.anonymous

    def init_name_dict(self):
        self.init_bases()
        self.name_dict : Dict[Name, Declaration] = {}
    
    # SPECIAL STRUCTURES : Nat, String, Quot, List

    def init_bases(self):
        self.anonymous = Anonymous()
        self.level_zero = LevelZero()
        self.level_one = LevelSucc(self.level_zero)
        self.Prop = Sort(self.level_zero)
        self.Type = Sort(self.level_one)

        # Lean constants
        self.Lean_name = string_to_name("Lean")

        # Nat constants
        self.Nat_name = string_to_name("Nat")
        self.Nat_zero_name = SubName(self.Nat_name, "zero")
        self.Nat_succ_name = SubName(self.Nat_name, "succ")

        self.Nat_add_name = SubName(self.Nat_name, "add")
        self.Nat_sub_name = SubName(self.Nat_name, "sub")
        self.Nat_mul_name = SubName(self.Nat_name, "mul")
        self.Nat_pow_name = SubName(self.Nat_name, "pow")
        self.Nat_gcd_name = SubName(self.Nat_name, "gcd")
        self.Nat_div_name = SubName(self.Nat_name, "div")
        self.Nat_eq_name = SubName(self.Nat_name, "beq")
        self.Nat_le_name = SubName(self.Nat_name, "ble")
        self.Nat_mod_name = SubName(self.Nat_name, "mod")
        self.Nat_beq_name = SubName(self.Nat_name, "beq")
        self.Nat_ble_name = SubName(self.Nat_name, "ble")
        self.Nat_land_name = SubName(self.Nat_name, "land")
        self.Nat_lor_name = SubName(self.Nat_name, "lor")
        self.Nat_lxor_name = SubName(self.Nat_name, "xor")
        self.Nat_shiftl_name = SubName(self.Nat_name, "shiftLeft")
        self.Nat_shiftr_name = SubName(self.Nat_name, "shiftRight")

        self.Nat_reduce_name = SubName(self.Lean_name, "reduceNat")

        # String constants
        self.String_name = string_to_name("String")
        self.String_mk_name = SubName(self.String_name, "mk")
        
        # List constants
        self.List_name = string_to_name("List")
        self.List_nil_name = SubName(self.List_name, "nil")
        self.List_cons_name = SubName(self.List_name, "cons")
        self.Char_name = string_to_name("Char")

        # Quot constants
        self.Quot_name = string_to_name("Quot")
        self.Quot_mk_name = SubName(self.Quot_name, "mk")
        self.Quot_lift_name = SubName(self.Quot_name, "lift")
        self.Quot_ind_name = SubName(self.Quot_name, "ind")

        # Bool constants
        self.Bool_name = string_to_name("Bool")
        self.Bool_true_name = SubName(self.Bool_name, "true")
        self.Bool_false_name = SubName(self.Bool_name, "false")
        
        self.Bool_reduce_name = SubName(self.Lean_name, "reduceBool")

        self.filler_name = string_to_name("filler")
        self.filler_const = Const(self.filler_name, [])

    def get_declaration_under_name(self, name : Name) -> Declaration:
        if name not in self.name_dict:
            raise ValueError(f"Name {name} does not exist in environment.")
        found = self.name_dict[name]
        if self.checking_inductive:
            if isinstance(found, Inductive):
                if not found.is_checked:
                    raise ValueError(f"Inductive type {name} has not been checked.")
            elif isinstance(found, Constructor):
                if not found.is_checked:
                    raise ValueError(f"Constructor {name} has not been checked.")
        
        return found
    
    def add_declaration(self, decl : Declaration):
        if decl.info.ciname in self.name_dict:
            raise ValueError(f"Name {decl.info.ciname} already exists in environment.")
        if (len(self.name_dict) + 1) % 100 == 0:
            print(f"Added {len(self.name_dict) + 1} declarations.")
        self.name_dict[decl.info.ciname] = decl
    
    def exists_declaration_under_name(self, name : Name) -> bool:
        return name in self.name_dict
    