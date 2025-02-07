from abc import abstractmethod
from typing import override
from LeanPy.Structures.Name import Name

class Level:
    def __init__(self):
        self.update_bookkeeping()
    
    def update_bookkeeping(self):
        """
        Updates the hash and number of metavariables in the level.
        """
        self.hash = self.get_hash()
        self.num_mvars = self.get_num_mvars()

    def __str__(self) -> str:
        raise NotImplementedError("Method __str__ not implemented for abstract class Level")

    @abstractmethod
    def structurally_equal(self, other: 'Level') -> bool:
        raise NotImplementedError("Method structurally_equal not implemented for abstract class Level")
    
    def __hash__(self) -> int: 
        return self.hash

    def get_num_mvars(self) -> int: 
        raise NotImplementedError("Method get_num_mvars not implemented for abstract class Level")

    def get_hash(self) -> int: 
        raise NotImplementedError("Method get_hash not implemented for abstract class Level")

class LevelZero(Level):
    @override
    def __init__(self):
        Level.__init__(self)
        
    @override
    def __str__(self) -> str:
        return "0"

    @override
    def structurally_equal(self, other: 'Level') -> bool:
        return isinstance(other, LevelZero)

    @override
    def get_hash(self) -> int: 
        return hash("Zero")

    @override
    def get_num_mvars(self) -> int: 
        return 0

class LevelSucc(Level):
    @override
    def __init__(self, anc: Level):
        self.anc = anc
        Level.__init__(self)
    
    @override
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

    @override
    def structurally_equal(self, other: 'Level') -> bool:
        return isinstance(other, LevelSucc) and self.anc.structurally_equal(other.anc)
    
    @override
    def get_hash(self) -> int: 
        return hash((self.anc, "Succ"))

    @override
    def get_num_mvars(self) -> int: 
        return self.anc.num_mvars

class LevelMax(Level):
    @override
    def __init__(self, lhs: Level, rhs: Level):
        self.lhs = lhs
        self.rhs = rhs
        Level.__init__(self)
    
    @override
    def __str__(self) -> str:
        return f"max ({self.lhs}) ({self.rhs})"

    @override
    def structurally_equal(self, other: 'Level') -> bool:
        return (
            isinstance(other, LevelMax) and 
            self.lhs.structurally_equal(other.lhs) and 
            self.rhs.structurally_equal(other.rhs)
        )
    
    @override
    def get_hash(self) -> int: 
        return hash((self.lhs, self.rhs, "Max"))

    @override
    def get_num_mvars(self) -> int: 
        return self.lhs.num_mvars + self.rhs.num_mvars

class LevelIMax(Level):
    @override
    def __init__(self, lhs: Level, rhs: Level):
        self.lhs = lhs
        self.rhs = rhs
        Level.__init__(self)
    
    @override
    def __str__(self) -> str:
        return f"imax ({self.lhs}) ({self.rhs})"

    @override
    def structurally_equal(self, other: 'Level') -> bool:
        return (
            isinstance(other, LevelIMax) and 
            self.lhs.structurally_equal(other.lhs) and 
            self.rhs.structurally_equal(other.rhs)
        )
    
    @override
    def get_hash(self) -> int: 
        return hash((self.lhs, self.rhs, "IMax"))

    @override
    def get_num_mvars(self) -> int: 
        return self.lhs.num_mvars + self.rhs.num_mvars

class LevelParam(Level):
    @override
    def __init__(self, pname: Name):
        self.pname = pname
        Level.__init__(self)
    
    @override
    def __str__(self) -> str:
        return f"{self.pname}"
    
    @override
    def structurally_equal(self, other: 'Level') -> bool:
        return isinstance(other, LevelParam) and self.pname == other.pname
    
    @override
    def get_hash(self) -> int: 
        return hash(("Param", self.pname))

    @override
    def get_num_mvars(self) -> int: 
        return 0

class LevelMVar(Level):
    @override
    def __init__(self):
        Level.__init__(self)
    
    @override
    def __str__(self) -> str: 
        return "?l"

    @override
    def get_hash(self) -> int: 
        return hash("MVar")

    @override
    def get_num_mvars(self) -> int: 
        return 1

level_constructors = [LevelZero, LevelSucc, LevelMax, LevelIMax, LevelParam]

__all__ = ['Level', 'LevelZero', 'LevelSucc', 'LevelMax', 'LevelIMax', 'LevelParam', 'level_constructors']