from abc import abstractmethod
from typing import List, Optional
from typing_extensions import override

from typeguard import typechecked

from Structures.Expression.Level import *
from Structures.Name import *

class Expression:
    @typechecked
    def __init__(self):
        self.hash = None
        
    @abstractmethod
    def get_hash(self) -> int:
        raise NotImplementedError(f"Method get_hash not implemented for class {self.__class__.__name__}")
    
    def __hash__(self) -> int:
        if self.hash is None:
            self.hash = self.get_hash()
        return self.hash

    @abstractmethod
    def __str__(self) -> str:
        raise NotImplementedError(f"Method __str__ not implemented for clas {self.__class__.__name__}")

class BVar(Expression):
    @typechecked
    def __init__(self, dbj_id : int):
        self.dbj_id = dbj_id
        Expression.__init__(self)
    
    @override
    def get_hash(self) -> int:
        return hash(("BVar", self.dbj_id))
    
    def __str__(self, depth : int = 0, is_start_of_newline : bool = True) -> str:
        return f"db{self.dbj_id}"

class FVar(Expression):
    @typechecked
    def __init__(self, name : Name, type : Expression, val : Optional[Expression], is_let : bool):
        #print(f"FVar created with id {hex(id(self))} and name {name}")
        self.name = name
        self.type = type
        self.val = val
        self.is_let = is_let
        Expression.__init__(self)

    def full_identifier(self) -> str:
        return f"{self.name}-{hex(id(self))}"# : ({self.type}) := ({self.val})"
    
    def full_print(self) -> str:
        return f"{self.full_identifier()} : ({self.type}) := ({self.val})"

    @override
    def get_hash(self) -> int:
        return hash(("FVar", hash(self.name)))
    
    def __str__(self) -> str:
        return self.full_identifier()

class Sort(Expression):
    @typechecked
    def __init__(self, level : Level):
        self.level = level
        Expression.__init__(self)
    
    @override
    def get_hash(self) -> int:
        return hash(("Sort", self.level))
    
    def __str__(self) -> str:
        return f"Sort {self.level}"
    
class Const(Expression):
    @typechecked
    def __init__(self, name : Name, lvl_params : List[Level]):
        self.name = name
        self.lvl_params = lvl_params
        Expression.__init__(self)
    
    @override
    def get_hash(self) -> int:
        return hash(("Const", hash(self.name)))
    
    def __str__(self) -> str:
        return f"{self.name}.{{{', '.join(map(str, self.lvl_params))}}}"
    
class App(Expression):
    @typechecked
    def __init__(self, fn : Expression, arg : Expression):
        self.fn = fn
        self.arg = arg
        Expression.__init__(self)
    
    @override
    def get_hash(self) -> int:
        return hash(("App", hash(self.fn), hash(self.arg)))
    
    def __str__(self) -> str:
        return f"({self.fn}) ({self.arg})"

class Pi(Expression):
    @typechecked
    def __init__(self, bname : Name, arg_type : Expression, body_type : Expression):
        self.bname = bname
        self.arg_type = arg_type
        self.body_type = body_type
        Expression.__init__(self)
    
    @override
    def get_hash(self) -> int:
        return hash(("Pi", hash(self.arg_type), hash(self.body_type)))
    
    def __str__(self) -> str:
        return f"({self.bname} : {self.arg_type}) -> ({self.body_type})"
    
class Lambda(Expression):
    @typechecked
    def __init__(self, bname : Name, arg_type : Expression, body : Expression):
        self.bname = bname
        self.arg_type = arg_type
        self.body = body
        Expression.__init__(self)
    
    @override
    def get_hash(self) -> int:
        return hash(("Lambda", hash(self.arg_type), hash(self.body)))
    
    def __str__(self) -> str:
        return f"fun ({self.bname} : {self.arg_type}) => ({self.body})"

class Let(Expression):
    @typechecked
    def __init__(self, bname : Name, arg_type : Expression, val : Expression, body : Expression):
        self.bname = bname
        self.arg_type = arg_type
        self.val = val
        self.body = body
        Expression.__init__(self)
    
    @override
    def get_hash(self) -> int:
        return hash(("Let", hash(self.bname), hash(self.arg_type), hash(self.val), hash(self.body)))
    
    def __str__(self) -> str:
        return f"(let {self.bname} : {self.arg_type} := {self.val}) in ({self.body})"

class Proj(Expression):
    @typechecked
    def __init__(self, type_name : Name, index : int, struct : Expression):
        self.type_name = type_name
        self.index = index
        self.struct = struct
        Expression.__init__(self)
    
    def get_hash(self) -> int:
        return hash(("Proj", hash(self.type_name), self.index, hash(self.struct)))
    
    def __str__(self) -> str:
        return f"({self.struct}).{self.index}"

class NatLit(Expression):
    @typechecked
    def __init__(self, val : int):
        assert val >= 0, "Natural number literals must be non-negative"
        self.val = val
        Expression.__init__(self)
    
    @override
    def get_hash(self) -> int:
        return hash(("NatLit", self.val))
    
    def __str__(self) -> str:
        return str(self.val)

class StringLit(Expression):
    @typechecked
    def __init__(self, val : str):
        self.val = val
        Expression.__init__(self)
    
    @override
    def get_hash(self) -> int:
        return hash(("StringLit", self.val))

    def __str__(self) -> str:
        return f'"{self.val}"'

__all__ = [
    'Expression', 
    'BVar', 
    'FVar', 
    'Sort', 
    'Const', 
    'App', 
    'Pi', 
    'Lambda', 
    'Let', 
    'Proj', 
    'NatLit', 
    'StringLit'
]