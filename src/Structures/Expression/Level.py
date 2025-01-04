from typeguard import typechecked

from Structures.Name import Name

class Level:
    def __str__(self) -> str:
        raise NotImplementedError("Method __str__ not implemented for abstract class Level")

    @typechecked
    def totally_equal(self, other: 'Level') -> bool:
        raise NotImplementedError("Method totally_equal not implemented for abstract class Level")
    
    def __hash__(self) -> int:
        if not hasattr(self, 'hash'):
            self.hash = self.get_hash()
        return self.hash

    def get_hash(self) -> int:
        raise NotImplementedError("Method get_hash not implemented for abstract class Level")
    
    def clone(self) -> 'Level':
        raise NotImplementedError("Method clone not implemented for abstract class Level")

class LevelZero(Level):
    def __str__(self) -> str:
        return "0"

    def totally_equal(self, other: 'Level') -> bool:
        return isinstance(other, LevelZero)

    def get_hash(self) -> int:
        return hash("Zero")
    
    def clone(self):
        return LevelZero()

class LevelSucc(Level):
    @typechecked
    def __init__(self, anc: Level):
        self.anc = anc
    
    def __str__(self) -> str:
        r = self
        o = 0
        while isinstance(r, LevelSucc):
            o += 1
            r = r.anc
        if isinstance(r, LevelZero):
            return f"{o}"
        else:
            return f"{o} + {r}"

    def totally_equal(self, other: 'Level') -> bool:
        return isinstance(other, LevelSucc) and self.anc.totally_equal(other.anc)
    
    def get_hash(self) -> int:
        return hash((self.anc, "Succ"))
    
    def clone(self):
        return LevelSucc(self.anc.clone())
    
class LevelMax(Level):
    @typechecked
    def __init__(self, lhs: Level, rhs: Level):
        self.lhs = lhs
        self.rhs = rhs
    
    def __str__(self) -> str:
        return f"Max({self.lhs}, {self.rhs})"

    def totally_equal(self, other: 'Level') -> bool:
        return isinstance(other, LevelMax) and self.lhs.totally_equal(other.lhs) and self.rhs.totally_equal(other.rhs)
    
    def get_hash(self) -> int:
        return hash((self.lhs, self.rhs, "Max"))
    
    def clone(self):
        return LevelMax(self.lhs.clone(), self.rhs.clone())

class LevelIMax(Level):
    @typechecked
    def __init__(self, lhs: Level, rhs: Level):
        self.lhs = lhs
        self.rhs = rhs
    
    def __str__(self) -> str:
        return f"IMax({self.lhs}, {self.rhs})"

    def totally_equal(self, other: 'Level') -> bool:
        return isinstance(other, LevelIMax) and self.lhs.totally_equal(other.lhs) and self.rhs.totally_equal(other.rhs)
    
    def get_hash(self) -> int:
        return hash((self.lhs, self.rhs, "IMax"))
    
    def clone(self):
        return LevelIMax(self.lhs.clone(), self.rhs.clone())

class LevelParam(Level):
    @typechecked
    def __init__(self, name: Name):
        self.name = name
    
    def __str__(self) -> str:
        return f"{self.name}"
    
    @typechecked
    def totally_equal(self, other: 'Level') -> bool:
        return isinstance(other, LevelParam) and self.name==other.name
    
    def get_hash(self) -> int:
        return hash(("Param", self.name))
    
    def clone(self):
        return LevelParam(self.name)

__all__ = ['Level', 'LevelZero', 'LevelSucc', 'LevelMax', 'LevelIMax', 'LevelParam']    