from abc import abstractmethod
from typeguard import typechecked

class Name:
    @abstractmethod
    def __str__(self) -> str:
        raise NotImplementedError("Method __str__ not implemented for abstract class Name")
    
    @typechecked
    def defEq(self, other: 'Name') -> bool:
        return self.__str__() == other.__str__()
    
    def __eq__(self, other: object) -> bool:
        if self is other: return True
        if not isinstance(other, Name): return False
        return self.defEq(other)
    
    def __hash__(self) -> int:
        return hash(self.__str__())

class Anonymous(Name):
    def __str__(self) -> str:
        return ""

class SubName(Name):
    @typechecked
    def __init__(self, anc : Name, str : str):
        self.str = str
        self.anc = anc
        self.full_str = f"{self.anc}.{self.str}"
    
    def __str__(self) -> str:
        return self.full_str

def string_to_name(s : str) -> Name:
    parts = s.split(".")
    cur = Anonymous()
    for part in parts:
        cur = SubName(cur, part)
    return cur
        

__all__ = ['Name', 'Anonymous', 'SubName']