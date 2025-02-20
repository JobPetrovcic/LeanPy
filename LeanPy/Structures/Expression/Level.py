from typing import Optional, override

from typeguard import typechecked
from LeanPy.Structures.Name import Name

class Level:
    @typechecked
    def __init__(self, source : Optional['Level']):
        self.is_external = False
        self.is_expected_type = False
        self.source = source if source is not None else self

        self.update_bookkeeping()
    
    def update_bookkeeping(self):
        """
        Updates the hash and number of metavariables in the level.
        """
        self.hash = self.get_hash()
        self.num_mvars = self.get_num_mvars()

    def __str__(self) -> str:
        raise NotImplementedError("Method __str__ not implemented for abstract class Level")
    
    def __hash__(self) -> int: 
        return self.hash

    def get_num_mvars(self) -> int: 
        raise NotImplementedError("Method get_num_mvars not implemented for abstract class Level")

    def get_hash(self) -> int: 
        raise NotImplementedError("Method get_hash not implemented for abstract class Level")
    
    @property
    def has_mvars(self) -> bool:
        return self.num_mvars > 0

class LevelZero(Level):
    @override
    @typechecked
    def __init__(self, source : Optional['Level']):
        Level.__init__(self, source)
        
    @override
    def __str__(self) -> str:
        return "0"

    @override
    def get_hash(self) -> int: 
        return hash("Zero")

    @override
    def get_num_mvars(self) -> int: 
        return 0

class LevelSucc(Level):
    @override
    @typechecked
    def __init__(self, anc: Level, source : Optional['Level']):
        self.anc = anc
        Level.__init__(self, source)
    
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
    def get_hash(self) -> int: 
        return hash((self.anc, "Succ"))

    @override
    def get_num_mvars(self) -> int: 
        return self.anc.num_mvars

class LevelMax(Level):
    @override
    @typechecked
    def __init__(self, lhs: Level, rhs: Level, source : Optional['Level']):
        self.lhs = lhs
        self.rhs = rhs
        Level.__init__(self, source)
    
    @override
    def __str__(self) -> str:
        return f"max ({self.lhs}) ({self.rhs})"

    @override
    def get_hash(self) -> int: 
        return hash((self.lhs, self.rhs, "Max"))

    @override
    def get_num_mvars(self) -> int: 
        return self.lhs.num_mvars + self.rhs.num_mvars

class LevelIMax(Level):
    @override
    @typechecked
    def __init__(self, lhs: Level, rhs: Level, source : Optional['Level']):
        self.lhs = lhs
        self.rhs = rhs
        Level.__init__(self, source)
    
    @override
    def __str__(self) -> str:
        return f"imax ({self.lhs}) ({self.rhs})"

    @override
    def get_hash(self) -> int: 
        return hash((self.lhs, self.rhs, "IMax"))

    @override
    def get_num_mvars(self) -> int: 
        return self.lhs.num_mvars + self.rhs.num_mvars

class LevelParam(Level):
    @override
    @typechecked
    def __init__(self, pname: Name, source : Optional['Level']):
        self.pname = pname
        Level.__init__(self, source)
    
    @override
    def __str__(self) -> str:
        return f"{self.pname}"

    @override
    def get_hash(self) -> int: 
        return hash(("Param", self.pname))

    @override
    def get_num_mvars(self) -> int: 
        return 0

class LevelMVar(Level):
    @override
    @typechecked
    def __init__(self, source : Optional['Level']):
        Level.__init__(self, source)
    
    @override
    def __str__(self) -> str: 
        return "?l"

    @override
    def get_hash(self) -> int: 
        return hash("MVar")

    @override
    def get_num_mvars(self) -> int: 
        return 1
    
    def structurally_equal(self, other: 'Level') -> bool:
        return self is other

level_constructors = [LevelZero, LevelSucc, LevelMax, LevelIMax, LevelParam]

__all__ = ['Level', 'LevelZero', 'LevelSucc', 'LevelMax', 'LevelIMax', 'LevelParam', 'LevelMVar', 'level_constructors']