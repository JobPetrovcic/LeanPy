from abc import abstractmethod

class Name:
    @abstractmethod
    def __str__(self) -> str:
        raise NotImplementedError("Method __str__ not implemented for abstract class Name")
    
    def __eq__(self, other: object) -> bool:
        if self is other: return True
        if not isinstance(other, Name): return False
        return self.__str__() == other.__str__()
    
    def __hash__(self) -> int:
        return hash(self.__str__())

class Anonymous(Name):
    def __str__(self) -> str:
        return "anon"

class SubName(Name):
    def __init__(self, anc : Name, str : str):
        self.str = str
        self.anc = anc
        if isinstance(anc, Anonymous):
            self.full_str = str
        else:
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