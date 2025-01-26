from Structures.Environment.Declaration.Declaration import Constructor, Declaration as Declaration, Definition as Definition, Inductive, Opaque as Opaque, Quot as Quot, Theorem as Theorem
from Structures.Expression.Expression import Const as Const, Expression as Expression
from Structures.Expression.Level import Level as Level
from Structures.Name import Anonymous, Name as Name
from _typeshed import Incomplete

class Environment:
    checking_inductive: bool
    def __init__(self) -> None: ...
    def get_anonymous(self) -> Anonymous: ...
    name_dict: Incomplete
    def init_name_dict(self) -> None: ...
    def create_name_from_str(self, name_str: str) -> Name: ...
    anonymous: Incomplete
    level_zero: Incomplete
    level_one: Incomplete
    Prop: Incomplete
    Type: Incomplete
    Lean_name: Incomplete
    Nat_name: Incomplete
    Nat_zero_name: Incomplete
    Nat_succ_name: Incomplete
    Nat_add_name: Incomplete
    Nat_sub_name: Incomplete
    Nat_mul_name: Incomplete
    Nat_pow_name: Incomplete
    Nat_gcd_name: Incomplete
    Nat_div_name: Incomplete
    Nat_eq_name: Incomplete
    Nat_le_name: Incomplete
    Nat_mod_name: Incomplete
    Nat_beq_name: Incomplete
    Nat_ble_name: Incomplete
    Nat_land_name: Incomplete
    Nat_lor_name: Incomplete
    Nat_lxor_name: Incomplete
    Nat_shiftl_name: Incomplete
    Nat_shiftr_name: Incomplete
    Nat_reduce_name: Incomplete
    String_name: Incomplete
    String_mk_name: Incomplete
    List_name: Incomplete
    List_nil_name: Incomplete
    List_cons_name: Incomplete
    Char_name: Incomplete
    Quot_name: Incomplete
    Quot_mk_name: Incomplete
    Quot_lift_name: Incomplete
    Quot_ind_name: Incomplete
    Bool_name: Incomplete
    Bool_true_name: Incomplete
    Bool_false_name: Incomplete
    Bool_reduce_name: Incomplete
    def init_bases(self) -> None: ...
    def get_declaration_under_name(self, name: Name) -> Declaration: ...
    def exists_declaration_under_name(self, name: Name) -> bool: ...
    def get_declaration_type_with_substituted_level_params(self, decl: Declaration, subs: list[Level]) -> Expression: ...
    def get_declaration_val_with_substituted_level_params(self, decl: Definition | Theorem | Opaque, subs: list[Level]) -> Expression: ...
    def get_constant_type(self, c: Const) -> Expression: ...
    def get_inductive(self, name: Name) -> Inductive: ...
    def get_constructor(self, name: Name) -> Constructor: ...
    def add_declaration(self, name: Name, decl: Declaration): ...
    def add_quot_declaration(self, name: Name, decl: Quot): ...
