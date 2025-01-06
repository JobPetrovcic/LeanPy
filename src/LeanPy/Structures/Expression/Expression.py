from abc import abstractmethod
from typing import List, Optional
from typing_extensions import override

from typeguard import typechecked

from LeanPy.Structures.Expression.Level import *
from LeanPy.Structures.Name import *

class Expression:
    @typechecked
    def __init__(self):
        self.hash = self.get_hash()
        self.update_bookkeeping()

    def update_bookkeeping(self):
        self.hash = self.get_hash()

        self.num_fvars = self.get_num_fvars()
        self.num_bvars = self.get_num_bvars()
        self.num_mvars = self.get_num_mvars()

        self.num_lvl_mvars = self.get_lvl_mvars()

    def get_num_fvars(self) -> int: raise NotImplementedError(f"Method get_num_fvars not implemented for class {self.__class__.__name__}")
    def get_num_bvars(self) -> int: raise NotImplementedError(f"Method get_num_bvars not implemented for class {self.__class__.__name__}")
    def get_num_mvars(self) -> int: raise NotImplementedError(f"Method get_num_mvars not implemented for class {self.__class__.__name__}")
    def get_lvl_mvars(self) -> int: raise NotImplementedError(f"Method get_lvl_mvars not implemented for class {self.__class__.__name__}")

    @abstractmethod
    def get_hash(self) -> int: raise NotImplementedError(f"Method get_hash not implemented for class {self.__class__.__name__}")
    
    def __hash__(self) -> int:
        return self.hash

    @abstractmethod
    def __str__(self) -> str:
        raise NotImplementedError(f"Method __str__ not implemented for clas {self.__class__.__name__}")
    
    @abstractmethod
    def totally_equal(self, other : 'Expression') -> bool:
        raise NotImplementedError(f"Method __eq__ not implemented for class {self.__class__.__name__}")
    
    def __eq__(self, other : object) -> bool:
        if self is other: return True
        if not isinstance(other, Expression): return False
        # compare the hashes first
        if hash(self) != hash(other): return False
        return self.totally_equal(other)

class BVar(Expression):
    @typechecked
    def __init__(self, dbj_id : int):
        self.dbj_id = dbj_id
        Expression.__init__(self)
    
    @override
    def get_hash(self) -> int: return hash(("BVar", self.dbj_id))
    def get_num_fvars(self): return 0
    def get_num_bvars(self): return 1
    def get_num_mvars(self): return 0
    def get_lvl_mvars(self): return 0
    
    def __str__(self, depth : int = 0, is_start_of_newline : bool = True) -> str:
        return f"db{self.dbj_id}"
    
    @typechecked
    def totally_equal(self, other : 'Expression') -> bool:
        return isinstance(other, BVar) and self.dbj_id == other.dbj_id

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
        return f"{'let ' if self.is_let else ''}{self.full_identifier()} : ({self.type}) := ({self.val})"

    @override
    def get_hash(self) -> int: return hash(("FVar", id(self)))
    def get_num_fvars(self): return 1
    def get_num_bvars(self): return 0
    def get_num_mvars(self): return 0
    def get_lvl_mvars(self): return 0
    
    def __str__(self) -> str:
        return f"F{self.name}" + (f":= {self.val}" if self.val is not None else "")
    
    @typechecked
    def totally_equal(self, other : 'Expression') -> bool:
        return self is other

class Sort(Expression):
    @typechecked
    def __init__(self, level : Level):
        self.level = level
        Expression.__init__(self)
    
    @override
    def get_hash(self) -> int: return hash(("Sort", self.level))
    def get_num_fvars(self): return 0
    def get_num_bvars(self): return 0
    def get_num_mvars(self): return 0
    def get_lvl_mvars(self): return self.level.num_mvars

    def __str__(self) -> str:
        return f"Sort {self.level}"
    
    @typechecked
    def totally_equal(self, other : 'Expression') -> bool:
        return isinstance(other, Sort) and self.level.totally_equal(other.level)
    
class Const(Expression):
    @typechecked
    def __init__(self, name : Name, lvl_params : List[Level]):
        self.name = name
        self.lvl_params = lvl_params
        Expression.__init__(self)
    
    @override
    def get_hash(self) -> int: return hash(("Const", hash(self.name)))
    def get_num_fvars(self): return 0
    def get_num_bvars(self): return 0
    def get_num_mvars(self): return 0
    def get_lvl_mvars(self): return sum([lvl.num_mvars for lvl in self.lvl_params])
    
    def __str__(self) -> str:
        return f"{self.name}.{{{', '.join(map(str, self.lvl_params))}}}"
    
    @typechecked
    def totally_equal(self, other : 'Expression') -> bool:
        return isinstance(other, Const) and self.name == other.name and len(self.lvl_params) == len(other.lvl_params) and all([l1.totally_equal(l2) for l1, l2 in zip(self.lvl_params, other.lvl_params)])
    
class App(Expression):
    @typechecked
    def __init__(self, fn : Expression, arg : Expression):
        self.fn = fn
        self.arg = arg
        Expression.__init__(self)
    
    @override
    def get_hash(self) -> int: return hash(("App", hash(self.fn), hash(self.arg)))
    def get_num_fvars(self): return self.fn.num_fvars + self.arg.num_fvars
    def get_num_bvars(self): return self.fn.num_bvars + self.arg.num_bvars
    def get_num_mvars(self): return self.fn.num_mvars + self.arg.num_mvars
    def get_lvl_mvars(self): return self.fn.num_lvl_mvars + self.arg.num_lvl_mvars
    
    def __str__(self) -> str:
        args : List[Expression] = []
        fn = self
        while isinstance(fn, App):
            args.append(fn.arg)
            fn = fn.fn
        return f"({fn} |> {'|> '.join(map(str, args))})"
    
    @typechecked
    def totally_equal(self, other : 'Expression') -> bool:
        return isinstance(other, App) and self.fn.totally_equal(other.fn) and self.arg.totally_equal(other.arg)

class Pi(Expression):
    @typechecked
    def __init__(self, bname : Name, arg_type : Expression, body_type : Expression):
        self.bname = bname
        self.arg_type = arg_type
        self.body_type = body_type
        Expression.__init__(self)
    
    @override
    def get_hash(self) -> int: return hash(("Pi", hash(self.arg_type), hash(self.body_type)))
    def get_num_fvars(self): return self.arg_type.num_fvars + self.body_type.num_fvars
    def get_num_bvars(self): return self.arg_type.num_bvars + self.body_type.num_bvars
    def get_num_mvars(self): return self.arg_type.num_mvars + self.body_type.num_mvars
    def get_lvl_mvars(self): return self.arg_type.num_lvl_mvars + self.body_type.num_lvl_mvars
    
    def __str__(self) -> str:
        return f"({self.bname} : {self.arg_type}) -> ({self.body_type})"
    
    @typechecked
    def totally_equal(self, other : 'Expression') -> bool:
        return isinstance(other, Pi) and self.arg_type.totally_equal(other.arg_type) and self.body_type.totally_equal(other.body_type) # don't need to check bname
    
class Lambda(Expression):
    @typechecked
    def __init__(self, bname : Name, arg_type : Expression, body : Expression):
        self.bname = bname
        self.arg_type = arg_type
        self.body = body
        Expression.__init__(self)
    
    @override
    def get_hash(self) -> int: return hash(("Lambda", hash(self.arg_type), hash(self.body)))
    def get_num_fvars(self): return self.arg_type.num_fvars + self.body.num_fvars
    def get_num_bvars(self): return self.arg_type.num_bvars + self.body.num_bvars
    def get_num_mvars(self): return self.arg_type.num_mvars + self.body.num_mvars
    def get_lvl_mvars(self): return self.arg_type.num_lvl_mvars + self.body.num_lvl_mvars
    
    def __str__(self) -> str:
        return f"fun ({self.bname} : {self.arg_type}) => ({self.body})"
    
    @typechecked
    def totally_equal(self, other : 'Expression') -> bool:
        return isinstance(other, Lambda) and self.arg_type.totally_equal(other.arg_type) and self.body.totally_equal(other.body) # don't need to check bname

class Let(Expression):
    @typechecked
    def __init__(self, bname : Name, arg_type : Expression, val : Expression, body : Expression):
        self.bname = bname
        self.arg_type = arg_type
        self.val = val
        self.body = body
        Expression.__init__(self)
    
    @override
    def get_hash(self) -> int: return hash(("Let", hash(self.bname), hash(self.arg_type), hash(self.val), hash(self.body)))
    def get_num_fvars(self): return self.arg_type.num_fvars + self.val.num_fvars + self.body.num_fvars
    def get_num_bvars(self): return self.arg_type.num_bvars + self.val.num_bvars + self.body.num_bvars
    def get_num_mvars(self): return self.arg_type.num_mvars + self.val.num_mvars + self.body.num_mvars
    def get_lvl_mvars(self): return self.arg_type.num_lvl_mvars + self.val.num_lvl_mvars + self.body.num_lvl_mvars
    
    def __str__(self) -> str:
        return f"(let {self.bname} : {self.arg_type} := {self.val}) in ({self.body})"
    
    @typechecked
    def totally_equal(self, other : 'Expression') -> bool:
        return isinstance(other, Let) and self.arg_type.totally_equal(other.arg_type) and self.val.totally_equal(other.val) and self.body.totally_equal(other.body) # don't need to check bname

class Proj(Expression):
    @typechecked
    def __init__(self, type_name : Name, index : int, struct : Expression):
        self.type_name = type_name
        self.index = index
        self.struct = struct
        Expression.__init__(self)
    
    def get_hash(self) -> int: return hash(("Proj", hash(self.type_name), self.index, hash(self.struct)))
    def get_num_fvars(self): return self.struct.num_fvars
    def get_num_bvars(self): return self.struct.num_bvars
    def get_num_mvars(self): return self.struct.num_mvars
    
    def __str__(self) -> str:
        return f"({self.struct}).{self.index}"
    
    @typechecked
    def totally_equal(self, other : 'Expression') -> bool:
        return isinstance(other, Proj) and self.type_name == other.type_name and self.index == other.index and self.struct.totally_equal(other.struct) # check the name since it refers to the structure we are projecting

class NatLit(Expression):
    @typechecked
    def __init__(self, val : int):
        assert val >= 0, "Natural number literals must be non-negative"
        self.val = val
        Expression.__init__(self)
    
    @override
    def get_hash(self) -> int: return hash(("NatLit", self.val))
    def get_num_fvars(self): return 0
    def get_num_bvars(self): return 0
    def get_num_mvars(self): return 0
    def get_lvl_mvars(self): return 0
    
    def __str__(self) -> str:
        return str(self.val)
    
    @typechecked
    def totally_equal(self, other : 'Expression') -> bool:
        return isinstance(other, NatLit) and self.val == other.val

class StringLit(Expression):
    @typechecked
    def __init__(self, val : str):
        self.val = val
        Expression.__init__(self)
    
    @override
    def get_hash(self) -> int: return hash(("StringLit", self.val))
    def get_num_fvars(self): return 0
    def get_num_bvars(self): return 0
    def get_num_mvars(self): return 0
    def get_lvl_mvars(self): return 0

    def __str__(self) -> str:
        return f'"{self.val}"'
    
    @typechecked
    def totally_equal(self, other : 'Expression') -> bool:
        return isinstance(other, StringLit) and self.val == other.val
    
class MVar(Expression):
    def __init__(self):
        Expression.__init__(self)
    
    @override
    def get_hash(self) -> int:return hash("MVar")
    def get_num_fvars(self): return 0
    def get_num_bvars(self): return 0
    def get_num_mvars(self): return 1
    def get_lvl_mvars(self): return 0
    
    def __str__(self) -> str: return "MVar"

__all__ = ['Expression', 'BVar', 'FVar', 'Sort', 'Const', 'App', 'Pi', 'Lambda', 'Let', 'Proj', 'NatLit', 'StringLit', 'MVar']