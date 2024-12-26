from typeguard import typechecked
from Structures.Environment.ReducibilityHint import ReducibilityHint
from Structures.Name import Name
from Structures.Expression.Expression import Expression
from Structures.Expression.Level import Level
from typing import List

class RecursionRule:
    @typechecked
    def __init__(self, constructor: Name, num_args: int, value: Expression):
        self.constructor = constructor
        assert num_args >= 0
        self.num_args = num_args
        self.value = value

class DeclarationInfo:
    @typechecked
    def __init__(self, name: Name, lvl_params : List[Level], type : Expression):
        self.name = name
        self.lvl_params = lvl_params
        self.type = type
    
    def __str__(self):
        return f"\tDeclarationInfo: \n\t\tName: {self.name}\n\t\tLevel Params: {self.lvl_params}\n\t\tType: {self.type}"

class Declaration:
    def __init__(self, info : DeclarationInfo):
        self.info = info
    
    def get_type(self) -> Expression:
        return self.info.type

class Axiom(Declaration):
    @typechecked
    def __init__(self, info : DeclarationInfo):
        super().__init__(info)

class Definition(Declaration):
    @typechecked
    def __init__(self, info: DeclarationInfo, value: Expression, hint: ReducibilityHint):
        super().__init__(info)
        self.value = value
        self.hint = hint

class Theorem(Declaration):
    @typechecked
    def __init__(self, info: DeclarationInfo, value: Expression):
        super().__init__(info)
        self.value = value

class Opaque(Declaration):
    @typechecked
    def __init__(self, info: DeclarationInfo, value: Expression):
        super().__init__(info)
        self.value = value

class Quot(Declaration):
    @typechecked
    def __init__(self, info: DeclarationInfo):
        super().__init__(info)

class InductiveType(Declaration):
    @typechecked
    def __init__(
        self, 
        info: DeclarationInfo, 
        is_recursive: bool, # this is not provided in the Lean 4 code, nor is it used in the kernel
        num_params: int, 
        num_indices: int,
        all_inductive_names: List[Name], 
        constructor_names: List[Name]
    ):
        super().__init__(info)
        self.is_recursive = is_recursive
        self.num_params = num_params
        self.num_indices = num_indices
        self.all_inductive_names = all_inductive_names
        self.constructor_names = constructor_names
    
    def number_of_constructors(self) -> int:
        return len(self.constructor_names)
    
    def get_ith_constructor_name(self, i: int) -> Name:
        assert i>=0, "Constructor index must be non-negative."
        if i < self.number_of_constructors(): 
            raise ValueError(f"Constructor index {i} is out of bounds.")
        return self.constructor_names[i]

class Constructor(Declaration):
    @typechecked
    def __init__(self, info: DeclarationInfo, inductive_name: Name, num_params: int, num_fields: int):
        super().__init__(info)
        self.inductive_name = inductive_name
        self.num_params = num_params
        self.num_fields = num_fields

class Recursor(Declaration):
    @typechecked
    def __init__(self, info: DeclarationInfo, num_params: int, num_indices: int, num_motives: int,
                    num_minors: int, recursion_rules: List["RecursionRule"], isK: bool):
        super().__init__(info)
        self.num_params = num_params
        self.num_indices = num_indices
        self.num_motives = num_motives
        self.num_minors = num_minors
        self.recursion_rules = recursion_rules
        self.isK = isK
    
    def __str__(self):
        return f"Recursor:\n{self.info}\n\tParams: {self.num_params}\n\tIndices: {self.num_indices}\n\tMotives: {self.num_motives}\n\tMinors: {self.num_minors}\n\tRules: {self.recursion_rules}\n\tisK: {self.isK}"