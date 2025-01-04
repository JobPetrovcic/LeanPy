from abc import abstractmethod
from typeguard import typechecked
from Structures.Environment.ReducibilityHint import Abbrev, OpaqueHint, ReducibilityHint, Regular
from Structures.Expression.ExpressionManipulation import get_app_function, get_binding_body, get_binding_type
from Kernel.KernelErrors import PanicError
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

    def get_height(self) -> int:
        return self.get_hint().get_height()

    @abstractmethod
    def has_value(self, allow_opaque : bool = False) -> bool:
        raise NotImplementedError("Method has_value not implemented for abstract class Declaration")
    
    def get_hint(self) -> "ReducibilityHint":
        if isinstance(self, Definition):
            return self.hint
        else:
            return OpaqueHint()

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

        self.is_checked : bool = False
    
    def number_of_constructors(self) -> int:
        return len(self.constructor_names)
    
    def get_ith_constructor_name(self, i: int) -> Name:
        assert i>=0, "Constructor index must be non-negative."
        if i < self.number_of_constructors(): 
            raise ValueError(f"Constructor index {i} is out of bounds.")
        return self.constructor_names[i]

    def has_value(self, allow_opaque : bool = False) -> bool:
        return False
    
    def __str__(self):
        return f"InductiveType:\n{self.info}\n\tParams: {self.num_params}\n\tIndices: {self.num_indices}\n\tConstructors: {[str(n) for n in self.constructor_names]}\n\tRecursive: {self.is_recursive}"      

class Constructor(Declaration):
    @typechecked
    def __init__(self, info: DeclarationInfo, c_index : int, inductive_name: Name, num_params: int, num_fields: int):
        super().__init__(info)
        self.inductive_name = inductive_name
        self.c_index = c_index
        self.num_params = num_params
        self.num_fields = num_fields

        self.is_checked : bool = False
    
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
    
    def get_major_index(self) -> int:
        """ Returns the index of the major premise -- the argument for which we want the inductive proof (technically type, which is more general than a proof). Suppose we have an inductive type and an application of its recursor. Then there are first num_params parameters' arguments, then num_indices indices' arguments, then num_motives motives' arguments, then num_minors minor premises arguments. Finally, the next argument is the major premise.
        Example:
            Nat.rec takes no parameters, no indices, a motive (P : Nat -> Type)
            Then follow two premises:
            - premise for 0: P 0 (proof/type that P holds for 0)
            - premise for succ: (n : Nat) -> P n -> P (succ n) (induction step)
            The next arguments is the major premise is the next argument -- the argument for which we actually want to prove the motive.
        """
        return self.num_params + self.num_motives + self.num_minors + self.num_indices
    
    def get_major_induct(self) -> Name: # DOES NOT CHANGE ANYTHING
        n = self.get_major_index()
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


def compare_reducibility_hints(d1 : Declaration, d2 : Declaration) -> int:
    h1 = d1.get_hint()
    h2 = d2.get_hint()

    if h1.__class__ == h2.__class__:
        if isinstance(h1, Regular):
            assert isinstance(h2, Regular)
            if h1.depth == h2.depth:
                return 0 # unfold both
            elif h1.depth > h2.depth:
                return -1 # unfold d1
            else: 
                return 1
        else:
            return 0 # reduce both
    else:
        if isinstance(h1, Opaque):
            return 1 # reduce d2
        elif isinstance(h2, Opaque):
            return -1 # reduce d1
        elif isinstance(h1, Abbrev):
            return -1 # reduce d1
        elif isinstance(h2, Abbrev):
            return 1 # reduce d2
        else:
            raise PanicError(f"Unreachable code reached in compare_reducibility_hints by comparing {h1} and {h2}.")

__all__ = ["Declaration", "Axiom", "Definition", "Theorem", "Opaque", "Quot", "InductiveType", "Constructor", "Recursor", "DeclarationInfo", "RecursionRule"]