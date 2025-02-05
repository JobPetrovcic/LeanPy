from abc import abstractmethod
from LeanPy.Structures.Name import Name

class Level:
    def __init__(self):
        self.update_bookkeeping()
    
    def update_bookkeeping(self):
        self.hash = self.get_hash()
        self.num_mvars = self.get_num_mvars()

    def __str__(self) -> str:
        raise NotImplementedError("Method __str__ not implemented for abstract class Level")

    @abstractmethod
    def totally_equal(self, other: 'Level') -> bool:
        raise NotImplementedError("Method totally_equal not implemented for abstract class Level")
    
    def __hash__(self) -> int: return self.hash
    def get_num_mvars(self) -> int: raise NotImplementedError("Method get_num_mvars not implemented for abstract class Level")
    def get_hash(self) -> int: raise NotImplementedError("Method get_hash not implemented for abstract class Level")

class LevelZero(Level):
    def __init__(self):
        Level.__init__(self)
        
    def __str__(self) -> str:
        return "0"

    def totally_equal(self, other: 'Level') -> bool:
        return isinstance(other, LevelZero)

    def get_hash(self) -> int: return hash("Zero")
    def get_num_mvars(self) -> int: return 0

class LevelSucc(Level):
    def __init__(self, anc: Level):
        self.anc = anc
        Level.__init__(self)
    
    def __str__(self) -> str:
        r = self
        o = 0
        while isinstance(r, LevelSucc):
            o += 1
            r = r.anc
        if isinstance(r, LevelZero):
            return f"{o}"
        else:
            return f"{r} + {o}"

    def totally_equal(self, other: 'Level') -> bool:
        return isinstance(other, LevelSucc) and self.anc.totally_equal(other.anc)
    
    def get_hash(self) -> int: return hash((self.anc, "Succ"))
    def get_num_mvars(self) -> int: return self.anc.num_mvars
    
class LevelMax(Level):
    def __init__(self, lhs: Level, rhs: Level):
        self.lhs = lhs
        self.rhs = rhs
        Level.__init__(self)
    
    def __str__(self) -> str:
        return f"max ({self.lhs}) ({self.rhs})"

    def totally_equal(self, other: 'Level') -> bool:
        return isinstance(other, LevelMax) and self.lhs.totally_equal(other.lhs) and self.rhs.totally_equal(other.rhs)
    
    def get_hash(self) -> int: return hash((self.lhs, self.rhs, "Max"))
    def get_num_mvars(self) -> int: return self.lhs.num_mvars + self.rhs.num_mvars

class LevelIMax(Level):
    def __init__(self, lhs: Level, rhs: Level):
        self.lhs = lhs
        self.rhs = rhs
        Level.__init__(self)
    
    def __str__(self) -> str:
        return f"imax ({self.lhs}) ({self.rhs})"

    def totally_equal(self, other: 'Level') -> bool:
        return isinstance(other, LevelIMax) and self.lhs.totally_equal(other.lhs) and self.rhs.totally_equal(other.rhs)
    
    def get_hash(self) -> int: return hash((self.lhs, self.rhs, "IMax"))
    def get_num_mvars(self) -> int: return self.lhs.num_mvars + self.rhs.num_mvars

class LevelParam(Level):
    def __init__(self, pname: Name):
        self.pname = pname
        Level.__init__(self)
    
    def __str__(self) -> str:
        return f"{self.pname}"
    
    def totally_equal(self, other: 'Level') -> bool:
        return isinstance(other, LevelParam) and self.pname==other.pname
    
    def get_hash(self) -> int: return hash(("Param", self.pname))
    def get_num_mvars(self) -> int: return 0

class LevelMVar(Level):
    def __init__(self):
        Level.__init__(self)
    
    def __str__(self) -> str: return "?l"

    def get_hash(self) -> int: return hash("MVar")
    def get_num_mvars(self) -> int: return 1
level_constructors = [LevelZero, LevelSucc, LevelMax, LevelIMax, LevelParam]

__all__ = ['Level', 'LevelZero', 'LevelSucc', 'LevelMax', 'LevelIMax', 'LevelParam', 'level_constructors']    