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
    def __init__(self, ancestor : Name, name : str):
        self.name = name
        self.ancestor = ancestor
    
    def __str__(self) -> str:
        return f"{self.ancestor}.{self.name}"
    
__all__ = ['Name', 'Anonymous', 'SubName']