from abc import abstractmethod
from typing import List, Optional, Set, Tuple
from typing_extensions import override

#from typeguard import typechecked

from LeanPy.Structures.Expression.Level import *
from LeanPy.Structures.Name import *

EXPR_COMPARE_RAW_THRESHOLD = 100 # the threshold for when to compare expressions without using the cache

class MetaInfo:
    def __init__(self, meta_info : Optional['MetaInfo'] = None):
        # if meta_info is not None copy the values from the given meta_info
        self.func_that_changed: List[str] = [] if meta_info is None else meta_info.func_that_changed.copy()

    def add_func_that_changed(self, func_name : str):
        self.func_that_changed.append(func_name)

    def __str__(self) -> str:
        return f"MI({self.func_that_changed})"

class Expression:
    #@typechecked
    def __init__(self, meta_info : Optional[MetaInfo] = None):
        self.meta_info = MetaInfo(meta_info)
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
    
    def __debug_str__(self) -> str:
        ds = self.__str__() + f"<--{self.meta_info}"
        return f"({ds})"
    
    @abstractmethod
    def totally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]], use_cache : bool) -> bool:
        raise NotImplementedError(f"Method __eq__ not implemented for class {self.__class__.__name__}")
    
    ##@profile
    def __eq__(self, other : object) -> bool:
        assert isinstance(other, Expression), f"Cannot compare an Expression with a non-Expression object {other}"

        if self.expr_size != other.expr_size: return False
        # create a cache for pairs of expressions that have already been compared
        # NOTE: note that this cache uses MEMORY ADDRESSES of the expressions to since we are implementing __eq__ that would be called by the == operator
        compare_cache : Set[Tuple[int, int]] = set() 
        return self.check_cache_and_compare(other, compare_cache, self.expr_size >= EXPR_COMPARE_RAW_THRESHOLD)

    def check_cache_and_compare(self, other : 'Expression', compare_cache : Set[Tuple[int, int]], use_cache : bool) -> bool:
        if self is other: return True
        # compare the hashes first
        if hash(self) != hash(other): return False
        if self.__class__ != other.__class__: return False

        if use_cache:
            key = (id(self), id(other))
            if key in compare_cache: return True
            compare_cache.add(key)
        return self.totally_equal(other, compare_cache, use_cache)
    
    @property
    def has_loose_bvars(self) -> bool:
        """ Returns True if the given expression has any loose bound variables. """
        return self.bvar_range >= 0
    
    @property
    def has_expr_mvars(self) -> bool:
        """ Returns True if the given expression has any metavariables. """
        return self.num_mvars > 0
    
    @property
    def has_fvars(self) -> bool:
        """ Returns True if the given expression has any free variables. """
        return self.num_fvars > 0

class BVar(Expression):
    #@typechecked
    def __init__(self, db_index : int, meta_info: Optional[MetaInfo] = None):
        self.db_index = db_index
        Expression.__init__(self, meta_info)
    
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
    ##@profile
    def totally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]], use_cache : bool) -> bool:
        return isinstance(other, BVar) and self.db_index == other.db_index

class FVar(Expression):
    #@typechecked
    def __init__(self, name : Name, type : Expression, val : Optional[Expression], is_let : bool, meta_info: Optional[MetaInfo] = None):
        #print(f"FVar created with id {hex(id(self))} and name {name}")
        self.name = name
        self.type = type
        self.val = val
        self.is_let = is_let
        Expression.__init__(self, meta_info)

    def full_identifier(self) -> str:
        return f"{self.name}-{hex(id(self))}"
    
    def full_print(self) -> str:
        return f"{'Flet ' if self.is_let else ''}{self.full_identifier()} : ({self.type})" + (f" := ({self.val})" if self.val is not None else "")

    @override
    def get_hash(self) -> int: return hash(("FVar", id(self)))
    def get_num_fvars(self): return 1
    def get_num_bvars(self): return 0
    def get_bvar_range(self): return -1
    def get_num_mvars(self): return 0
    def get_lvl_mvars(self): return 0
    def get_expr_size(self) -> int: return 1
    
    def __str__(self) -> str:
        name_str = f"{self.name}"
        name_str = name_str.replace(".", "_").replace("@", "")
        return f"{name_str}" + (f":= {self.val}" if self.val is not None else "")
    
    #@typechecked
    ##@profile
    def totally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]], use_cache : bool) -> bool:
        return self is other

class Sort(Expression):
    #@typechecked
    def __init__(self, level : Level, meta_info: Optional[MetaInfo] = None):
        self.level = level
        Expression.__init__(self, meta_info)
    
    @override
    def get_hash(self) -> int: return hash(("Sort", self.level))
    def get_num_fvars(self): return 0
    def get_num_bvars(self): return 0
    def get_bvar_range(self): return -1
    def get_num_mvars(self): return 0
    def get_lvl_mvars(self): return self.level.num_mvars
    def get_expr_size(self) -> int: return 1

    def __str__(self) -> str:
        return f"(Sort ({self.level}))"
    
    #@typechecked
    ##@profile
    def totally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]], use_cache : bool) -> bool:
        return isinstance(other, Sort) and self.level.totally_equal(other.level)
    
class Const(Expression):
    #@typechecked
    def __init__(self, cname : Name, lvl_params : List[Level], meta_info: Optional[MetaInfo] = None):
        self.cname = cname
        self.lvl_params = lvl_params
        Expression.__init__(self, meta_info)
    
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
    ##@profile
    def totally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]], use_cache : bool) -> bool:
        return isinstance(other, Const) and self.cname == other.cname and len(self.lvl_params) == len(other.lvl_params) and all([l1.totally_equal(l2) for l1, l2 in zip(self.lvl_params, other.lvl_params)])
    
class App(Expression):
    #@typechecked
    def __init__(self, fn : Expression, arg : Expression, meta_info: Optional[MetaInfo] = None):
        self.fn = fn
        self.arg = arg
        Expression.__init__(self, meta_info)
    
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
    ##@profile
    def totally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]], use_cache : bool) -> bool:
        return isinstance(other, App) and self.fn.check_cache_and_compare(other.fn, compare_cache, use_cache) and self.arg.check_cache_and_compare(other.arg, compare_cache, use_cache)

class Pi(Expression):
    #@typechecked
    def __init__(self, bname : Name, domain : Expression, codomain : Expression, meta_info: Optional[MetaInfo] = None):
        self.bname = bname
        self.domain = domain
        self.codomain = codomain
        Expression.__init__(self, meta_info)
    
    @override
    def get_hash(self) -> int: return hash(("Pi", hash(self.domain), hash(self.codomain)))
    def get_num_fvars(self): return self.domain.num_fvars + self.codomain.num_fvars
    def get_num_bvars(self): return self.domain.num_bvars + self.codomain.num_bvars
    def get_bvar_range(self): return max(self.domain.bvar_range, self.codomain.bvar_range-1)
    def get_num_mvars(self): return self.domain.num_mvars + self.codomain.num_mvars
    def get_lvl_mvars(self): return self.domain.num_lvl_mvars + self.codomain.num_lvl_mvars
    def get_expr_size(self) -> int: return self.domain.expr_size + self.codomain.expr_size + 1
    
    def __str__(self) -> str:
        bname_str = f"{self.bname}"
        bname_str = bname_str.replace(".", "_").replace("@", "")
        return f"({bname_str} : {self.domain}) -> ({self.codomain})"
    
    #@typechecked
    ##@profile
    def totally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]], use_cache : bool) -> bool:
        return isinstance(other, Pi) and self.domain.check_cache_and_compare(other.domain, compare_cache, use_cache) and self.codomain.check_cache_and_compare(other.codomain, compare_cache, use_cache)
    
class Lambda(Expression):
    #@typechecked
    def __init__(self, bname : Name, domain : Expression, body : Expression, meta_info: Optional[MetaInfo] = None):
        self.bname = bname
        self.domain = domain
        self.body = body
        Expression.__init__(self, meta_info)
    
    @override
    def get_hash(self) -> int: return hash(("Lambda", hash(self.domain), hash(self.body)))
    def get_num_fvars(self): return self.domain.num_fvars + self.body.num_fvars
    def get_num_bvars(self): return self.domain.num_bvars + self.body.num_bvars
    def get_bvar_range(self): return max(self.domain.bvar_range, self.body.bvar_range-1)
    def get_num_mvars(self): return self.domain.num_mvars + self.body.num_mvars
    def get_lvl_mvars(self): return self.domain.num_lvl_mvars + self.body.num_lvl_mvars
    def get_expr_size(self) -> int: return self.domain.expr_size + self.body.expr_size + 1
    
    def __str__(self) -> str:
        bname_str = f"{self.bname}"
        bname_str = bname_str.replace(".", "_").replace("@", "")
        return f"(fun ({bname_str} : {self.domain}) => ({self.body}))"
    
    #@typechecked
    ##@profile
    def totally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]], use_cache : bool) -> bool:
        return isinstance(other, Lambda) and self.domain.check_cache_and_compare(other.domain, compare_cache, use_cache) and self.body.check_cache_and_compare(other.body, compare_cache, use_cache)
    
class Let(Expression):
    #@typechecked
    def __init__(self, bname : Name, domain : Expression, val : Expression, body : Expression, meta_info: Optional[MetaInfo] = None):
        self.bname = bname
        self.domain = domain
        self.val = val
        self.body = body
        Expression.__init__(self, meta_info)
    
    @override
    def get_hash(self) -> int: return hash(("Let", hash(self.bname), hash(self.domain), hash(self.val), hash(self.body)))
    def get_num_fvars(self): return self.domain.num_fvars + self.val.num_fvars + self.body.num_fvars
    def get_num_bvars(self): return self.domain.num_bvars + self.val.num_bvars + self.body.num_bvars
    def get_bvar_range(self): return max(self.domain.bvar_range, self.val.bvar_range, self.body.bvar_range-1)
    def get_num_mvars(self): return self.domain.num_mvars + self.val.num_mvars + self.body.num_mvars
    def get_lvl_mvars(self): return self.domain.num_lvl_mvars + self.val.num_lvl_mvars + self.body.num_lvl_mvars
    def get_expr_size(self) -> int: return self.domain.expr_size + self.val.expr_size + self.body.expr_size + 1
    
    def __str__(self) -> str:
        return f"(let {self.bname} : {self.domain} := {self.val}) in ({self.body})"
    
    #@typechecked
    ##@profile
    def totally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]], use_cache : bool) -> bool:
        return isinstance(other, Let) and self.domain.check_cache_and_compare(other.domain, compare_cache, use_cache) and self.val.check_cache_and_compare(other.val, compare_cache, use_cache) and self.body.check_cache_and_compare(other.body, compare_cache, use_cache)
    
class Proj(Expression):
    #@typechecked
    def __init__(self, sname : Name, index : int, expr : Expression, meta_info: Optional[MetaInfo] = None):
        self.sname = sname
        self.index = index
        self.expr = expr
        Expression.__init__(self, meta_info)
    
    def get_hash(self) -> int: return hash(("Proj", hash(self.sname), self.index, hash(self.expr)))
    def get_num_fvars(self): return self.expr.num_fvars
    def get_num_bvars(self): return self.expr.num_bvars
    def get_bvar_range(self): return self.expr.bvar_range
    def get_num_mvars(self): return self.expr.num_mvars
    def get_lvl_mvars(self): return self.expr.num_lvl_mvars
    def get_expr_size(self) -> int: return self.expr.expr_size + 1
    
    def __str__(self) -> str:
        return f"({self.expr}).{self.index + 1}"
    
    #@typechecked
    ##@profile
    def totally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]], use_cache : bool) -> bool:
        return isinstance(other, Proj) and self.sname == other.sname and self.index == other.index and self.expr.check_cache_and_compare(other.expr, compare_cache, use_cache)
    
class NatLit(Expression):
    #@typechecked
    def __init__(self, val : int, meta_info: Optional[MetaInfo] = None):
        assert val >= 0, "Natural number literals must be non-negative"
        self.val = val
        Expression.__init__(self, meta_info)
    
    @override
    def get_hash(self) -> int: return hash(("NatLit", self.val))
    def get_num_fvars(self): return 0
    def get_num_bvars(self): return 0
    def get_bvar_range(self): return -1
    def get_num_mvars(self): return 0
    def get_lvl_mvars(self): return 0
    def get_expr_size(self) -> int: return 1

    def __str__(self) -> str:
        return "N"+str(self.val)
    
    #@typechecked
    ##@profile
    def totally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]], use_cache : bool) -> bool:
        return isinstance(other, NatLit) and self.val == other.val

class StrLit(Expression):
    #@typechecked
    def __init__(self, val : str, meta_info: Optional[MetaInfo] = None):
        self.val = val
        Expression.__init__(self, meta_info)
    
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
    ##@profile
    def totally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]], use_cache : bool) -> bool:
        return isinstance(other, StrLit) and self.val == other.val
    
class MVar(Expression):
    def __init__(self, meta_info: Optional[MetaInfo] = None):
        Expression.__init__(self, meta_info)
    
    @override
    def get_hash(self) -> int: return hash("MVar")
    def get_num_fvars(self): return 0
    def get_num_bvars(self): return 0
    def get_bvar_range(self): return -1
    def get_num_mvars(self): return 1
    def get_lvl_mvars(self): return 0
    def get_expr_size(self) -> int: return 1
    
    def __str__(self) -> str: return "MVar"

expr_constructors = [BVar, FVar, Sort, Const, App, Pi, Lambda, Let, Proj, NatLit, StrLit]
__all__ = ['Expression', 'BVar', 'FVar', 'Sort', 'Const', 'App', 'Pi', 'Lambda', 'Let', 'Proj', 'NatLit', 'StrLit', 'MVar', 'expr_constructors']