from abc import abstractmethod
from typeguard import typechecked
from Structures.Environment.ReducibilityHint import ReducibilityHint
from Structures.Expression.ExpressionManipulation import get_app_function, get_binding_body, get_binding_type
from Structures.Name import Name
from Structures.Expression.Expression import *
from Structures.Expression.Level import LevelParam
from typing import List, Optional

class RecursionRule:
    @typechecked
    def __init__(self, constructor: Name, num_fields: int, value: Expression):
        self.constructor = constructor
        assert num_fields >= 0
        self.num_fields = num_fields
        self.value = value

    def __str__(self):
        return f"\tRecursionRule for {self.constructor} with {self.num_fields} args:\n\t\t{self.value}"

class DeclarationInfo:
    @typechecked
    def __init__(self, name: Name, lvl_params : List[LevelParam], type : Expression):
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

    @abstractmethod
    def has_value(self, allow_opaque : bool = False) -> bool:
        raise NotImplementedError("Method has_value not implemented for abstract class Declaration")

class Axiom(Declaration):
    @typechecked
    def __init__(self, info : DeclarationInfo):
        super().__init__(info)
    
    def has_value(self, allow_opaque : bool = False) -> bool:
        return False

class Definition(Declaration):
    @typechecked
    def __init__(self, info: DeclarationInfo, value: Expression, hint: ReducibilityHint):
        super().__init__(info)
        self.value = value
        self.hint = hint
    
    def has_value(self, allow_opaque : bool = False) -> bool:
        return True

class Theorem(Declaration):
    @typechecked
    def __init__(self, info: DeclarationInfo, value: Expression):
        super().__init__(info)
        self.value = value
    
    def has_value(self, allow_opaque : bool = False) -> bool:
        return True

class Opaque(Declaration):
    @typechecked
    def __init__(self, info: DeclarationInfo, value: Expression):
        super().__init__(info)
        self.value = value
    
    def has_value(self, allow_opaque : bool = False) -> bool:
        return allow_opaque

class Quot(Declaration):
    @typechecked
    def __init__(self, info: DeclarationInfo):
        super().__init__(info)
    
    def has_value(self, allow_opaque : bool = False) -> bool:
        return False

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

    def has_value(self, allow_opaque : bool = False) -> bool:
        return False

class Constructor(Declaration):
    @typechecked
    def __init__(self, info: DeclarationInfo, inductive_name: Name, num_params: int, num_fields: int):
        super().__init__(info)
        self.inductive_name = inductive_name
        self.num_params = num_params
        self.num_fields = num_fields
    
    def has_value(self, allow_opaque : bool = False) -> bool:
        return False

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
        rrs = ''.join(["\t\t"+str(rr)+"\n" for rr in self.recursion_rules])
        return f"Recursor:\n{self.info}\n\tParams: {self.num_params}\n\tIndices: {self.num_indices}\n\tMotives: {self.num_motives}\n\tMinors: {self.num_minors}\n\tRules: {rrs}\n\tisK: {self.isK}"
    
    @typechecked
    def has_value(self, allow_opaque : bool = False) -> bool:
        return False
    
    def get_major_idx(self) -> int:
        return self.num_params + self.num_motives + self.num_minors + self.num_indices
    
    def get_major_induct(self) -> Name:
        n = self.get_major_idx()
        t = self.info.type

        for _ in range(n):
            t = get_binding_body(t)
 
        t = get_binding_type(t)
        fn = get_app_function(t)
        if not isinstance(fn, Const):
            raise ValueError(f"Expected Const, got {fn} when decomposing major premise of recursor.")
        
        return fn.name
    
    @typechecked
    def get_recursion_rule(self, major : Expression) -> Optional[RecursionRule]:
        fn = get_app_function(major)
        if not isinstance(fn, Const): return None
        for rule in self.recursion_rules:
            if rule.constructor == fn.name:
                return rule
        return None


__all__ = ["Declaration", "Axiom", "Definition", "Theorem", "Opaque", "Quot", "InductiveType", "Constructor", "Recursor", "DeclarationInfo", "RecursionRule"]