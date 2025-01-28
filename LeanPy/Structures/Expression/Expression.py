from abc import abstractmethod
from typing import List, Optional, Set, Tuple
from typing_extensions import override

#from typeguard import typechecked

from LeanPy.Structures.Expression.Level import *
from LeanPy.Structures.Name import *

class Expression:
    #@typechecked
    def __init__(self):
        self.update_bookkeeping()

    def update_bookkeeping(self):
        self.hash = self.get_hash()

        self.num_fvars = self.get_num_fvars()
        self.num_bvars = self.get_num_bvars()
        self.bvar_range = self.get_bvar_range() # the maximum bvar index in the expression, adjusted for the number of binders
        self.num_mvars = self.get_num_mvars()

        self.num_lvl_mvars = self.get_lvl_mvars()

        self.expr_size = self.get_expr_size()

    def get_num_fvars(self) -> int: raise NotImplementedError(f"Method get_num_fvars not implemented for class {self.__class__.__name__}")
    def get_num_bvars(self) -> int: raise NotImplementedError(f"Method get_num_bvars not implemented for class {self.__class__.__name__}")
    def get_bvar_range(self) -> int: raise NotImplementedError(f"Method get_bvar_range not implemented for class {self.__class__.__name__}")
    def get_num_mvars(self) -> int: raise NotImplementedError(f"Method get_num_mvars not implemented for class {self.__class__.__name__}")
    def get_lvl_mvars(self) -> int: raise NotImplementedError(f"Method get_lvl_mvars not implemented for class {self.__class__.__name__}")
    def get_expr_size(self) -> int: raise NotImplementedError(f"Method get_expr_size not implemented for class {self.__class__.__name__}")

    @abstractmethod
    def get_hash(self) -> int: raise NotImplementedError(f"Method get_hash not implemented for class {self.__class__.__name__}")
    
    def __hash__(self) -> int:
        return self.hash

    @abstractmethod
    def __str__(self) -> str:
        raise NotImplementedError(f"Method __str__ not implemented for clas {self.__class__.__name__}")
    
    @abstractmethod
    def totally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]]) -> bool:
        raise NotImplementedError(f"Method __eq__ not implemented for class {self.__class__.__name__}")
    
    @profile
    def __eq__(self, other : object) -> bool:
        assert isinstance(other, Expression), f"Cannot compare an Expression with a non-Expression object {other}"

        # create a cache for pairs of expressions that have already been compared
        # NOTE: note that this cache uses MEMORY ADDRESSES of the expressions to since we are implementing __eq__ that would be called by the == operator
        compare_cache : Set[Tuple[int, int]] = set() 
        return self.check_cache_and_compare(other, compare_cache)

    def check_cache_and_compare(self, other : 'Expression', compare_cache : Set[Tuple[int, int]]) -> bool:
        if self is other: return True
        # compare the hashes first
        if hash(self) != hash(other): return False
        if self.__class__ != other.__class__: return False

        key = (id(self), id(other))

        if key in compare_cache: return True
        compare_cache.add(key)
        return self.totally_equal(other, compare_cache)

class BVar(Expression):
    #@typechecked
    def __init__(self, db_index : int):
        self.db_index = db_index
        Expression.__init__(self)
    
    @override
    def get_hash(self) -> int: return hash(("BVar", self.db_index))
    def get_num_fvars(self): return 0
    def get_num_bvars(self): return 1
    def get_bvar_range(self): return self.db_index
    def get_num_mvars(self): return 0
    def get_lvl_mvars(self): return 0
    def get_expr_size(self) -> int: return 1
    
    def __str__(self, depth : int = 0, is_start_of_newline : bool = True) -> str:
        return f"db{self.db_index}"
    
    #@typechecked
    #@profile
    def totally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]]) -> bool:
        return isinstance(other, BVar) and self.db_index == other.db_index

class FVar(Expression):
    #@typechecked
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
    def get_bvar_range(self): return -1
    def get_num_mvars(self): return 0
    def get_lvl_mvars(self): return 0
    def get_expr_size(self) -> int: return 1
    
    def __str__(self) -> str:
        return f"F{self.name}" + (f":= {self.val}" if self.val is not None else "")
    
    #@typechecked
    #@profile
    def totally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]]) -> bool:
        return self is other

class Sort(Expression):
    #@typechecked
    def __init__(self, level : Level):
        self.level = level
        Expression.__init__(self)
    
    @override
    def get_hash(self) -> int: return hash(("Sort", self.level))
    def get_num_fvars(self): return 0
    def get_num_bvars(self): return 0
    def get_bvar_range(self): return -1
    def get_num_mvars(self): return 0
    def get_lvl_mvars(self): return self.level.num_mvars
    def get_expr_size(self) -> int: return 1

    def __str__(self) -> str:
        return f"Sort {self.level}"
    
    #@typechecked
    #@profile
    def totally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]]) -> bool:
        return isinstance(other, Sort) and self.level.totally_equal(other.level)
    
class Const(Expression):
    #@typechecked
    def __init__(self, cname : Name, lvl_params : List[Level]):
        self.cname = cname
        self.lvl_params = lvl_params
        Expression.__init__(self)
    
    @override
    def get_hash(self) -> int: return hash(("Const", hash(self.cname)))
    def get_num_fvars(self): return 0
    def get_num_bvars(self): return 0
    def get_bvar_range(self): return -1
    def get_num_mvars(self): return 0
    def get_lvl_mvars(self): return sum([lvl.num_mvars for lvl in self.lvl_params])
    def get_expr_size(self) -> int: return 1
    
    def __str__(self) -> str:
        const_str = f"@{self.cname}"
        if len(self.lvl_params) == 0: return const_str
        params_str = f"{{{', '.join(map(str, self.lvl_params))}}}"
        return f"{const_str}.{params_str}"
    
    #@typechecked
    #@profile
    def totally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]]) -> bool:
        return isinstance(other, Const) and self.cname == other.cname and len(self.lvl_params) == len(other.lvl_params) and all([l1.totally_equal(l2) for l1, l2 in zip(self.lvl_params, other.lvl_params)])
    
class App(Expression):
    #@typechecked
    def __init__(self, fn : Expression, arg : Expression):
        self.fn = fn
        self.arg = arg
        Expression.__init__(self)
    
    @override
    def get_hash(self) -> int: return hash(("App", hash(self.fn), hash(self.arg)))
    def get_num_fvars(self): return self.fn.num_fvars + self.arg.num_fvars
    def get_num_bvars(self): return self.fn.num_bvars + self.arg.num_bvars
    def get_bvar_range(self): return max(self.fn.bvar_range, self.arg.bvar_range)
    def get_num_mvars(self): return self.fn.num_mvars + self.arg.num_mvars
    def get_lvl_mvars(self): return self.fn.num_lvl_mvars + self.arg.num_lvl_mvars
    def get_expr_size(self) -> int: return self.fn.expr_size + self.arg.expr_size + 1
    
    def __str__(self) -> str:
        args : List[Expression] = []
        fn = self
        while isinstance(fn, App):
            args.append(fn.arg)
            fn = fn.fn
        args = list(reversed(args))
        return f"({fn} {' '.join(map(str, args))})"
    
    #@typechecked
    #@profile
    def totally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]]) -> bool:
        return isinstance(other, App) and self.fn.check_cache_and_compare(other.fn, compare_cache) and self.arg.check_cache_and_compare(other.arg, compare_cache)

class Pi(Expression):
    #@typechecked
    def __init__(self, bname : Name, arg_type : Expression, body_type : Expression):
        self.bname = bname
        self.arg_type = arg_type
        self.body_type = body_type
        Expression.__init__(self)
    
    @override
    def get_hash(self) -> int: return hash(("Pi", hash(self.arg_type), hash(self.body_type)))
    def get_num_fvars(self): return self.arg_type.num_fvars + self.body_type.num_fvars
    def get_num_bvars(self): return self.arg_type.num_bvars + self.body_type.num_bvars
    def get_bvar_range(self): return max(self.arg_type.bvar_range, self.body_type.bvar_range-1) # the -1 is because the argument is a binder
    def get_num_mvars(self): return self.arg_type.num_mvars + self.body_type.num_mvars
    def get_lvl_mvars(self): return self.arg_type.num_lvl_mvars + self.body_type.num_lvl_mvars
    def get_expr_size(self) -> int: return self.arg_type.expr_size + self.body_type.expr_size + 1
    
    def __str__(self) -> str:
        return f"({self.bname} : {self.arg_type}) -> ({self.body_type})"
    
    #@typechecked
    #@profile
    def totally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]]) -> bool:
        return isinstance(other, Pi) and self.arg_type.check_cache_and_compare(other.arg_type, compare_cache) and self.body_type.check_cache_and_compare(other.body_type, compare_cache) # don't need to check bname
    
class Lambda(Expression):
    #@typechecked
    def __init__(self, bname : Name, arg_type : Expression, body : Expression):
        self.bname = bname
        self.arg_type = arg_type
        self.body = body
        Expression.__init__(self)
    
    @override
    def get_hash(self) -> int: return hash(("Lambda", hash(self.arg_type), hash(self.body)))
    def get_num_fvars(self): return self.arg_type.num_fvars + self.body.num_fvars
    def get_num_bvars(self): return self.arg_type.num_bvars + self.body.num_bvars
    def get_bvar_range(self): return max(self.arg_type.bvar_range, self.body.bvar_range-1) # the -1 is because the argument is a binder
    def get_num_mvars(self): return self.arg_type.num_mvars + self.body.num_mvars
    def get_lvl_mvars(self): return self.arg_type.num_lvl_mvars + self.body.num_lvl_mvars
    def get_expr_size(self) -> int: return self.arg_type.expr_size + self.body.expr_size + 1
    
    def __str__(self) -> str:
        return f"fun ({self.bname} : {self.arg_type}) => ({self.body})"
    
    #@typechecked
    #@profile
    def totally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]]) -> bool:
        return isinstance(other, Lambda) and self.arg_type.check_cache_and_compare(other.arg_type, compare_cache) and self.body.check_cache_and_compare(other.body, compare_cache) # don't need to check bname

class Let(Expression):
    #@typechecked
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
    def get_bvar_range(self): return max(self.arg_type.bvar_range, self.val.bvar_range, self.body.bvar_range-1) # the -1 is because the argument is a binder
    def get_num_mvars(self): return self.arg_type.num_mvars + self.val.num_mvars + self.body.num_mvars
    def get_lvl_mvars(self): return self.arg_type.num_lvl_mvars + self.val.num_lvl_mvars + self.body.num_lvl_mvars
    def get_expr_size(self) -> int: return self.arg_type.expr_size + self.val.expr_size + self.body.expr_size + 1
    
    def __str__(self) -> str:
        return f"(let {self.bname} : {self.arg_type} := {self.val}) in ({self.body})"
    
    #@typechecked
    #@profile
    def totally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]]) -> bool:
        return isinstance(other, Let) and self.arg_type.check_cache_and_compare(other.arg_type, compare_cache) and self.val.check_cache_and_compare(other.val, compare_cache) and self.body.check_cache_and_compare(other.body, compare_cache) # don't need to check bname

class Proj(Expression):
    #@typechecked
    def __init__(self, sname : Name, index : int, expr : Expression):
        self.sname = sname
        self.index = index
        self.expr = expr
        Expression.__init__(self)
    
    def get_hash(self) -> int: return hash(("Proj", hash(self.sname), self.index, hash(self.expr)))
    def get_num_fvars(self): return self.expr.num_fvars
    def get_num_bvars(self): return self.expr.num_bvars
    def get_bvar_range(self): return self.expr.bvar_range
    def get_num_mvars(self): return self.expr.num_mvars
    def get_lvl_mvars(self): return self.expr.num_lvl_mvars
    def get_expr_size(self) -> int: return self.expr.expr_size + 1
    
    def __str__(self) -> str:
        return f"({self.expr}).{self.index}"
    
    #@typechecked
    #@profile
    def totally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]]) -> bool:
        return isinstance(other, Proj) and self.sname == other.sname and self.index == other.index and self.expr.check_cache_and_compare(other.expr, compare_cache) # check the name since it refers to the structure we are projecting

class NatLit(Expression):
    #@typechecked
    def __init__(self, val : int):
        assert val >= 0, "Natural number literals must be non-negative"
        self.val = val
        Expression.__init__(self)
    
    @override
    def get_hash(self) -> int: return hash(("NatLit", self.val))
    def get_num_fvars(self): return 0
    def get_num_bvars(self): return 0
    def get_bvar_range(self): return -1
    def get_num_mvars(self): return 0
    def get_lvl_mvars(self): return 0
    def get_expr_size(self) -> int: return 1

    def __str__(self) -> str:
        return str(self.val)
    
    #@typechecked
    #@profile
    def totally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]]) -> bool:
        return isinstance(other, NatLit) and self.val == other.val

class StrLit(Expression):
    #@typechecked
    def __init__(self, val : str):
        self.val = val
        Expression.__init__(self)
    
    @override
    def get_hash(self) -> int: return hash(("StringLit", self.val))
    def get_num_fvars(self): return 0
    def get_num_bvars(self): return 0
    def get_bvar_range(self): return -1
    def get_num_mvars(self): return 0
    def get_lvl_mvars(self): return 0
    def get_expr_size(self) -> int: return 1

    def __str__(self) -> str:
        return f'"{self.val}"'
    
    #@typechecked
    #@profile
    def totally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]]) -> bool:
        return isinstance(other, StrLit) and self.val == other.val
    
class MVar(Expression):
    def __init__(self):
        Expression.__init__(self)
    
    @override
    def get_hash(self) -> int:return hash("MVar")
    def get_num_fvars(self): return 0
    def get_num_bvars(self): return 0
    def get_bvar_range(self): return -1
    def get_num_mvars(self): return 1
    def get_lvl_mvars(self): return 0
    def get_expr_size(self) -> int: return 1
    
    def __str__(self) -> str: return "MVar"

expr_constructors = [BVar, FVar, Sort, Const, App, Pi, Lambda, Let, Proj, NatLit, StrLit]

__all__ = ['Expression', 'BVar', 'FVar', 'Sort', 'Const', 'App', 'Pi', 'Lambda', 'Let', 'Proj', 'NatLit', 'StrLit', 'expr_constructors']