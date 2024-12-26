from typing import Dict, List

from typeguard import typechecked

from Structures.Environment.Declaration import Constructor, Declaration, Definition, InductiveType, Theorem
from Structures.Expression.Expression import Const, Expression
from Structures.Expression.ExpressionManipulation import substitute_level_params_in_expression
from Structures.Expression.Level import Level
from Structures.Name import Anonymous, Name, SubName

class Environment:
    def __init__(self):
        
        self.init_name_dict()
    
    def get_anonymous(self) -> Anonymous:
        return self.anonymous

    def init_name_dict(self):
        self.anonymous = Anonymous()
        self.name_dict : Dict[Name, Declaration | None] = {Anonymous() : None}

        self.NatName = SubName(self.get_anonymous(), "Nat")
        self._add_subname(self.NatName, None)
        self.StringName = SubName(self.get_anonymous(), "String")
        self._add_subname(self.StringName, None)

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
    
    @typechecked
    def get_cloned_type_with_substituted_level_params(self, decl : Declaration, subs : List[Level]) -> Expression:
        if len(decl.info.lvl_params) != len(subs):
            print(f"decl parameters : {[str(l) for l in decl.info.lvl_params]}")
            print(f"subs parameters : {[str(l) for l in subs]}")
            raise ValueError(f"Declaration {decl} has {len(decl.info.lvl_params)} level parameters, but {len(subs)} substitutions were provided.")
        substitutions = list(zip(decl.info.lvl_params, subs))
        return substitute_level_params_in_expression(decl.get_type(), substitutions) # this clones the expression
    
    def get_cloned_val_with_substituted_level_params(self, decl : Definition | Theorem, subs : List[Level]) -> Expression:
        if len(decl.info.lvl_params) != len(subs):
            raise ValueError(f"Declaration {decl} has a different number of level parameters than the substitutions provided.")
        substitutions = list(zip(decl.info.lvl_params, subs))
        return substitute_level_params_in_expression(decl.value, substitutions) # this clones the expression
        
    def get_constant_type(self, c : Const) -> Expression:
        decl = self.get_declaration_under_name(c.name)

        return self.get_cloned_type_with_substituted_level_params(decl, c.lvl_params)

    def get_inductive(self, name : Name) -> InductiveType:
        decl = self.get_declaration_under_name(name)
        if not isinstance(decl, InductiveType):
            raise ValueError(f"Name {name} is not an inductive type.")
        return decl

    def get_constructor(self, name : Name) -> Constructor:
        decl = self.get_declaration_under_name(name)
        if not isinstance(decl, Constructor):
            raise ValueError(f"Name {name} is not a constructor.")
        return decl
    
    # adding declarations
    def add_declaration(self, name : Name, decl : Declaration):
        if name in self.name_dict:
            raise ValueError(f"Name {name} already exists in environment.")
        self.name_dict[name] = decl

#    class Axiom(Declaration):
#    @typechecked
#    def __init__(self, info : DeclarationInfo):
#        super().__init__(info)
#
#class Definition(Declaration):
#    @typechecked
#    def __init__(self, info: DeclarationInfo, value: Expression, hint: ReducibilityHint):
#        super().__init__(info)
#        self.value = value
#        self.hint = hint
#
#class Theorem(Declaration):
#    @typechecked
#    def __init__(self, info: DeclarationInfo, value: Expression):
#        super().__init__(info)
#        self.value = value
#
#class Opaque(Declaration):
#    @typechecked
#    def __init__(self, info: DeclarationInfo, value: Expression):
#        super().__init__(info)
#        self.value = value
#
#class Quot(Declaration):
#    @typechecked
#    def __init__(self, info: DeclarationInfo):
#        super().__init__(info)
#
#class InductiveType(Declaration):
#    @typechecked
#    def __init__(self, info: DeclarationInfo, is_recursive: bool, num_params: int, num_indices: int,
#                    all_inductive_names: List[Name], constructor_names: List[Name]):
#        super().__init__(info)
#        self.is_recursive = is_recursive
#        self.num_params = num_params
#        self.num_indices = num_indices
#        self.all_inductive_names = all_inductive_names
#        self.constructor_names = constructor_names
#
#class Constructor(Declaration):
#    @typechecked
#    def __init__(self, info: DeclarationInfo, inductive_name: Name, num_params: int, num_fields: int):
#        super().__init__(info)
#        self.inductive_name = inductive_name
#        self.num_params = num_params
#        self.num_fields = num_fields
#
#class Recursor(Declaration):
#    @typechecked
#    def __init__(self, info: DeclarationInfo, num_params: int, num_indices: int, num_motives: int,
#                    num_minors: int, recursion_rules: List["RecursionRule"], isK: bool):
#        super().__init__(info)
#        self.num_params = num_params
#        self.num_indices = num_indices
#        self.num_motives = num_motives
#        self.num_minors = num_minors
#        self.recursion_rules = recursion_rules
#        self.isK = isK