from abc import abstractmethod
from typing import Any, List, Optional, Set, Tuple
from typeguard import typechecked
from typing_extensions import override

#from typeguard import typechecked

from LeanPy.Structures.Expression.Level import *
from LeanPy.Structures.Expression.LevelManipulation import structurally_equal
from LeanPy.Structures.Name import *

EXPR_COMPARE_RAW_THRESHOLD = 100 # the threshold for when to compare expressions without using the cache

class Expression:
    @typechecked
    def __init__(self, source : Optional['Expression']):
        self.source = source if source is not None else self
        self.is_external = False
        self.is_expected_type = False
        self.update_bookkeeping()

    def update_bookkeeping(self):
        """
        Updates different bookkeeping attributes of the expression.
        """
        self.hash = self.get_hash()

        self.num_fvars = self.get_num_fvars()
        self.num_bvars = self.get_num_bvars()
        self.bvar_range = self.get_bvar_range() # the maximum bvar index in the expression, adjusted for the number of binders
        self.num_expr_mvars = self.get_num_expr_mvars()

        self.num_lvl_mvars = self.get_lvl_mvars()

        self.expr_size = self.get_expr_size()

    def get_num_fvars(self) -> int: 
        raise NotImplementedError(f"Method get_num_fvars not implemented for class {self.__class__.__name__}")
    def get_num_bvars(self) -> int: 
        raise NotImplementedError(f"Method get_num_bvars not implemented for class {self.__class__.__name__}")
    def get_bvar_range(self) -> int: 
        raise NotImplementedError(f"Method get_bvar_range not implemented for class {self.__class__.__name__}")
    def get_num_expr_mvars(self) -> int: 
        raise NotImplementedError(f"Method get_num_expr_mvars not implemented for class {self.__class__.__name__}")
    def get_lvl_mvars(self) -> int: 
        raise NotImplementedError(f"Method get_lvl_mvars not implemented for class {self.__class__.__name__}")
    def get_expr_size(self) -> int: 
        raise NotImplementedError(f"Method get_expr_size not implemented for class {self.__class__.__name__}")

    @abstractmethod
    def get_hash(self) -> int: 
        raise NotImplementedError(f"Method get_hash not implemented for class {self.__class__.__name__}")
    
    def __hash__(self) -> int:
        return self.hash

    @abstractmethod
    def __str__(self) -> str:
        raise NotImplementedError(f"Method __str__ not implemented for class {self.__class__.__name__}")
    
    @abstractmethod
    def structurally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]], use_cache : bool) -> bool:
        raise NotImplementedError(f"Method __eq__ not implemented for class {self.__class__.__name__}")
    
    def __eq__(self, other : object) -> bool:
        """
        Checks if the given expression is structurally equal to the other expression. If the expression is large, caching can be used to avoid comparing the same pair of expressions multiple times.
        """
        assert isinstance(other, Expression), f"Cannot compare an Expression with a non-Expression object {other}"

        if self.expr_size != other.expr_size: 
            return False
        # create a cache for pairs of expressions that have already been compared
        # NOTE: note that this cache uses MEMORY ADDRESSES of the expressions to since we are implementing __eq__ that would be called by the == operator
        compare_cache : Set[Tuple[int, int]] = set() 
        return self.check_cache_and_compare(other, compare_cache, self.expr_size >= EXPR_COMPARE_RAW_THRESHOLD)

    def check_cache_and_compare(self, other : 'Expression', compare_cache : Set[Tuple[int, int]], use_cache : bool) -> bool:
        """
        Checks if the given expression is structurally equal to the other expression. To avoid exponential blowup, caching can be used to avoid comparing the same pair of expressions multiple times.
        """
        if self is other: 
            return True
        # compare the hashes first
        if hash(self) != hash(other): 
            return False
        if self.__class__ != other.__class__: 
            return False

        if use_cache:
            key = (id(self), id(other))
            if key in compare_cache: 
                return True
            compare_cache.add(key)
        return self.structurally_equal(other, compare_cache, use_cache)
    
    @property
    def has_loose_bvars(self) -> bool:
        """ 
        Returns True if the given expression has any loose bound variables. 
        """
        return self.bvar_range >= 0
    
    @property
    def has_expr_mvars(self) -> bool:
        """ 
        Returns True if the given expression has any metavariables. 
        """
        return self.num_expr_mvars > 0
    
    @property
    def has_lvl_mvars(self) -> bool:
        """ 
        Returns True if the given expression has any level metavariables. 
        """
        return self.num_lvl_mvars > 0
    
    @property
    def has_mvars(self) -> bool:
        """ 
        Returns True if the given expression has any metavariables. 
        """
        return self.has_expr_mvars or self.has_lvl_mvars
    
    @property
    def has_fvars(self) -> bool:
        """ 
        Returns True if the given expression has any free variables. 
        """
        return self.num_fvars > 0

class BVar(Expression):
    @typechecked
    def __init__(self, db_index : int, source : Optional['Expression'] = None):
        self.db_index = db_index
        Expression.__init__(self, source)
    
    @override
    def get_hash(self) -> int: 
        return hash(("BVar", self.db_index))
    
    @override
    def get_num_fvars(self): 
        return 0
    
    @override
    def get_num_bvars(self): 
        return 1
    
    @override
    def get_bvar_range(self): 
        return self.db_index
    
    @override
    def get_num_expr_mvars(self): 
        return 0
    
    @override
    def get_lvl_mvars(self): 
        return 0
    
    @override
    def get_expr_size(self) -> int: 
        return 1
    
    @override
    def __str__(self) -> str:
        return f"db{self.db_index}"
    
    @override
    def structurally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]], use_cache : bool) -> bool:
        return isinstance(other, BVar) and self.db_index == other.db_index

class FVar(Expression):
    @typechecked
    def __init__(self, name : Name, type : Expression, original_type : Expression, val : Optional[Expression], original_val : Optional[Expression], is_let : bool, source : Optional['Expression'] = None):
        self.name = name
        self.type = type
        self.original_type = original_type
        self.val = val
        self.original_val = original_val
        self.is_let = is_let
        Expression.__init__(self, source)

    def full_identifier(self) -> str:
        return f"{self.name}-{hex(id(self))}"# : ({self.type}) := ({self.val})"
    
    def full_print(self) -> str:
        return f"{'Flet ' if self.is_let else ''}{self.full_identifier()} : ({self.type})" + (f" := ({self.val})" if self.val is not None else "")

    @override
    def get_hash(self) -> int: 
        return hash(("FVar", id(self)))
    
    @override
    def get_num_fvars(self): 
        return 1
    
    @override
    def get_num_bvars(self): 
        return 0
    
    @override
    def get_bvar_range(self): 
        return -1
    
    @override
    def get_num_expr_mvars(self): 
        return self.type.num_expr_mvars + (0 if self.val is None else self.val.num_expr_mvars)
    
    @override
    def get_lvl_mvars(self): 
        return self.type.num_lvl_mvars + (0 if self.val is None else self.val.num_lvl_mvars)
    
    @override
    def get_expr_size(self) -> int: 
        return 1
    
    @override
    def __str__(self) -> str:
        name_str = f"{self.name}"
        # replace . with _ in the name and remove @
        name_str = name_str.replace(".", "_").replace("@", "")
        return f"{name_str}" + (f":= {self.val}" if self.val is not None else "")
    
    @override
    def structurally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]], use_cache : bool) -> bool:
        return self is other

class Sort(Expression):
    @typechecked
    def __init__(self, level : Level, source : Optional['Expression'] = None):
        self.level = level
        Expression.__init__(self, source)
    
    @override
    def get_hash(self) -> int: 
        return hash(("Sort", hash(self.level)))
    
    @override
    def get_num_fvars(self): 
        return 0
    
    @override
    def get_num_bvars(self): 
        return 0
    
    @override
    def get_bvar_range(self): 
        return -1
    
    @override
    def get_num_expr_mvars(self): 
        return 0
    
    @override
    def get_lvl_mvars(self): 
        return self.level.num_mvars
    
    @override
    def get_expr_size(self) -> int: 
        return 1

    @override
    def __str__(self) -> str:
        return f"(Sort ({self.level}))"
    
    @override
    def structurally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]], use_cache : bool) -> bool:
        return isinstance(other, Sort) and structurally_equal(self.level, other.level, False)

class Const(Expression):
    @typechecked
    def __init__(self, cname : Name, lvl_params : List[Level], source : Optional['Expression'] = None):
        self.cname = cname
        self.lvl_params = lvl_params
        Expression.__init__(self, source)
    
    @override
    def get_hash(self) -> int:
        lvl_params_hash = tuple([hash(lvl) for lvl in self.lvl_params])

        return hash(("Const", hash(self.cname), lvl_params_hash))
    
    @override
    def get_num_fvars(self): 
        return 0
    
    @override
    def get_num_bvars(self): 
        return 0
    
    @override
    def get_bvar_range(self): 
        return -1
    
    @override
    def get_num_expr_mvars(self): 
        return 0
    
    @override
    def get_lvl_mvars(self): 
        return sum([lvl.num_mvars for lvl in self.lvl_params])
    
    @override
    def get_expr_size(self) -> int: 
        return 1
    
    @override
    def __str__(self) -> str:
        const_str = f"@{self.cname}"
        if len(self.lvl_params) == 0: 
            return const_str
        params_str = f"{{{', '.join(map(str, self.lvl_params))}}}"
        return f"{const_str}.{params_str}"
    
    @override
    def structurally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]], use_cache : bool) -> bool:
        return (isinstance(other, Const) and 
                self.cname == other.cname and 
                len(self.lvl_params) == len(other.lvl_params) and 
                all([structurally_equal(l1, l2, False) for l1, l2 in zip(self.lvl_params, other.lvl_params)]))
    
    # override __getattr__ so that levels parameters can be accessed as attributes
    def __getattr__(self, attr_name : str) -> Any:
        if attr_name == "lvl_params":
            return object.__getattribute__(self, attr_name)
        elif attr_name.startswith("lvl_"):
            lvl_index = int(attr_name[4:])
            if lvl_index < len(self.lvl_params):
                return self.lvl_params[lvl_index]
            else:
                raise AttributeError(f"Attribute {attr_name} not found in Const object {self}")
        elif attr_name == "cname":
            return self.cname
        return super().__getattr__(attr_name) # type: ignore

    # override __setattr__ so that levels parameters can be set as attributes
    def __setattr__(self, attr_name : str, value : Any) -> None:
        if attr_name == "lvl_params":
            object.__setattr__(self, attr_name, value)
        elif attr_name.startswith("lvl_"):
            lvl_index = int(attr_name[4:])
            assert 0 <= lvl_index
            if lvl_index < len(self.lvl_params):
                self.lvl_params[lvl_index] = value
            else:
                raise AttributeError(f"Cannot set attribute {attr_name} of Const object {self}")
        elif attr_name == "cname":
            assert isinstance(value, Name)
            object.__setattr__(self, attr_name, value)
        else:
            object.__setattr__(self, attr_name, value)

class App(Expression):
    @typechecked
    def __init__(self, fn : Expression, arg : Expression, source : Optional['Expression'] = None):
        self.fn = fn
        self.arg = arg
        Expression.__init__(self, source)
    
    @override
    def get_hash(self) -> int: 
        return hash(("App", hash(self.fn), hash(self.arg)))
    
    @override
    def get_num_fvars(self): 
        return self.fn.num_fvars + self.arg.num_fvars
    
    @override
    def get_num_bvars(self): 
        return self.fn.num_bvars + self.arg.num_bvars
    
    @override
    def get_bvar_range(self): 
        return max(self.fn.bvar_range, self.arg.bvar_range)
    
    @override
    def get_num_expr_mvars(self): 
        return self.fn.num_expr_mvars + self.arg.num_expr_mvars
    
    @override
    def get_lvl_mvars(self): 
        return self.fn.num_lvl_mvars + self.arg.num_lvl_mvars
    
    @override
    def get_expr_size(self) -> int: 
        return self.fn.expr_size + self.arg.expr_size + 1
    
    @override
    def __str__(self) -> str:
        args : List[Expression] = []
        fn = self
        while isinstance(fn, App):
            args.append(fn.arg)
            fn = fn.fn
        args = list(reversed(args))
        return f"(({fn}) {' '.join(map(str, args))})"
    
    @override
    def structurally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]], use_cache : bool) -> bool:
        return (isinstance(other, App) and 
                self.fn.check_cache_and_compare(other.fn, compare_cache, use_cache) and 
                self.arg.check_cache_and_compare(other.arg, compare_cache, use_cache))

class Pi(Expression):
    @typechecked
    def __init__(self, bname : Name, domain : Expression, codomain : Expression, source : Optional['Expression'] = None):
        self.bname = bname
        self.domain = domain
        self.codomain = codomain
        Expression.__init__(self, source)
    
    @override
    def get_hash(self) -> int: 
        return hash(("Pi", hash(self.domain), hash(self.codomain)))
    
    @override
    def get_num_fvars(self): 
        return self.domain.num_fvars + self.codomain.num_fvars
    
    @override
    def get_num_bvars(self): 
        return self.domain.num_bvars + self.codomain.num_bvars
    
    @override
    def get_bvar_range(self): 
        return max(self.domain.bvar_range, self.codomain.bvar_range-1) # the -1 is because the argument is a binder
    
    @override
    def get_num_expr_mvars(self): 
        return self.domain.num_expr_mvars + self.codomain.num_expr_mvars
    
    @override
    def get_lvl_mvars(self): 
        return self.domain.num_lvl_mvars + self.codomain.num_lvl_mvars
    
    @override
    def get_expr_size(self) -> int: 
        return self.domain.expr_size + self.codomain.expr_size + 1
    
    @override
    def __str__(self) -> str:
        bname_str = f"{self.bname}"
        # replace . with _ in the name
        bname_str = bname_str.replace(".", "_").replace("@", "")
        return f"({bname_str} : {self.domain}) -> ({self.codomain})"
    
    @override
    def structurally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]], use_cache : bool) -> bool:
        return (isinstance(other, Pi) and 
                self.domain.check_cache_and_compare(other.domain, compare_cache, use_cache) and 
                self.codomain.check_cache_and_compare(other.codomain, compare_cache, use_cache)) # don't need to check bname

class Lambda(Expression):
    @typechecked
    def __init__(self, bname : Name, domain : Expression, body : Expression, source : Optional['Expression'] = None):
        self.bname = bname
        self.domain = domain
        self.body = body
        Expression.__init__(self, source)
    
    @override
    def get_hash(self) -> int: 
        return hash(("Lambda", hash(self.domain), hash(self.body)))
    
    @override
    def get_num_fvars(self): 
        return self.domain.num_fvars + self.body.num_fvars
    
    @override
    def get_num_bvars(self): 
        return self.domain.num_bvars + self.body.num_bvars
    
    @override
    def get_bvar_range(self): 
        return max(self.domain.bvar_range, self.body.bvar_range-1) # the -1 is because the argument is a binder
    
    @override
    def get_num_expr_mvars(self): 
        return self.domain.num_expr_mvars + self.body.num_expr_mvars
    
    @override
    def get_lvl_mvars(self): 
        return self.domain.num_lvl_mvars + self.body.num_lvl_mvars
    
    @override
    def get_expr_size(self) -> int: 
        return self.domain.expr_size + self.body.expr_size + 1
    
    @override
    def __str__(self) -> str:
        bname_str = f"{self.bname}"
        # replace . with _ in the name
        bname_str = bname_str.replace(".", "_").replace("@", "")
        return f"(fun ({bname_str} : {self.domain}) => ({self.body}))"
    
    @override
    def structurally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]], use_cache : bool) -> bool:
        return (isinstance(other, Lambda) and 
                self.domain.check_cache_and_compare(other.domain, compare_cache, use_cache) and 
                self.body.check_cache_and_compare(other.body, compare_cache, use_cache)) # don't need to check bname

class Let(Expression):
    @typechecked
    def __init__(self, bname : Name, domain : Expression, val : Expression, body : Expression, source : Optional['Expression'] = None):
        self.bname = bname
        self.domain = domain
        self.val = val
        self.body = body
        Expression.__init__(self, source)
    
    @override
    def get_hash(self) -> int: 
        return hash(("Let", hash(self.domain), hash(self.val), hash(self.body)))
    
    @override
    def get_num_fvars(self): 
        return self.domain.num_fvars + self.val.num_fvars + self.body.num_fvars
    
    @override
    def get_num_bvars(self): 
        return self.domain.num_bvars + self.val.num_bvars + self.body.num_bvars
    
    @override
    def get_bvar_range(self): 
        return max(self.domain.bvar_range, self.val.bvar_range, self.body.bvar_range-1) # the -1 is because the argument is a binder
    
    @override
    def get_num_expr_mvars(self): 
        return self.domain.num_expr_mvars + self.val.num_expr_mvars + self.body.num_expr_mvars
    
    @override
    def get_lvl_mvars(self): 
        return self.domain.num_lvl_mvars + self.val.num_lvl_mvars + self.body.num_lvl_mvars
    
    @override
    def get_expr_size(self) -> int: 
        return self.domain.expr_size + self.val.expr_size + self.body.expr_size + 1
    
    @override
    def __str__(self) -> str:
        return f"(let {self.bname} : {self.domain} := {self.val}) in ({self.body})"
    
    @override
    def structurally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]], use_cache : bool) -> bool:
        return (isinstance(other, Let) and 
                self.domain.check_cache_and_compare(other.domain, compare_cache, use_cache) and 
                self.val.check_cache_and_compare(other.val, compare_cache, use_cache) and 
                self.body.check_cache_and_compare(other.body, compare_cache, use_cache)) # don't need to check bname

class Proj(Expression):
    @typechecked
    def __init__(self, sname : Name, index : int, expr : Expression, source : Optional['Expression'] = None):
        self.sname = sname
        self.index = index
        self.expr = expr
        Expression.__init__(self, source)
    
    @override
    def get_hash(self) -> int: 
        return hash(("Proj", hash(self.sname), self.index, hash(self.expr)))
    
    @override
    def get_num_fvars(self): 
        return self.expr.num_fvars
    
    @override
    def get_num_bvars(self): 
        return self.expr.num_bvars
    
    @override
    def get_bvar_range(self): 
        return self.expr.bvar_range
    
    @override
    def get_num_expr_mvars(self): 
        return self.expr.num_expr_mvars
    
    @override
    def get_lvl_mvars(self): 
        return self.expr.num_lvl_mvars
    
    @override
    def get_expr_size(self) -> int: 
        return self.expr.expr_size + 1
    
    @override
    def __str__(self) -> str:
        return f"({self.expr}).{self.index + 1}"
    
    @override
    def structurally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]], use_cache : bool) -> bool:
        return (isinstance(other, Proj) and 
                self.sname == other.sname and 
                self.index == other.index and 
                self.expr.check_cache_and_compare(other.expr, compare_cache, use_cache)) # check the name since it refers to the structure we are projecting

class NatLit(Expression):
    @typechecked
    def __init__(self, val : int, source : Optional['Expression'] = None):
        assert val >= 0, "Natural number literals must be non-negative"
        self.val = val
        Expression.__init__(self, source)
    
    @override
    def get_hash(self) -> int: 
        return hash(("NatLit", self.val))
    
    @override
    def get_num_fvars(self): 
        return 0
    
    @override
    def get_num_bvars(self): 
        return 0
    
    @override
    def get_bvar_range(self): 
        return -1
    
    @override
    def get_num_expr_mvars(self): 
        return 0
    
    @override
    def get_lvl_mvars(self): 
        return 0
    
    @override
    def get_expr_size(self) -> int: 
        return 1

    @override
    def __str__(self) -> str:
        return str(self.val)
    
    @override
    def structurally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]], use_cache : bool) -> bool:
        return isinstance(other, NatLit) and self.val == other.val

class StrLit(Expression):
    @typechecked
    def __init__(self, val : str, source : Optional['Expression'] = None):
        self.val = val
        Expression.__init__(self, source)
    
    @override
    def get_hash(self) -> int: 
        return hash(("StringLit", self.val))
    
    @override
    def get_num_fvars(self): 
        return 0
    
    @override
    def get_num_bvars(self): 
        return 0
    
    @override
    def get_bvar_range(self): 
        return -1
    
    @override
    def get_num_expr_mvars(self): 
        return 0
    
    @override
    def get_lvl_mvars(self): 
        return 0
    
    @override
    def get_expr_size(self) -> int: 
        return 1

    @override
    def __str__(self) -> str:
        return f'"{self.val}"'
    
    @override
    def structurally_equal(self, other : 'Expression', compare_cache : Set[Tuple[int, int]], use_cache : bool) -> bool:
        return isinstance(other, StrLit) and self.val == other.val
    
class MVar(Expression):
    @typechecked
    def __init__(self, source : Optional['Expression'] = None):
        Expression.__init__(self, source)
    
    @override
    def get_hash(self) -> int:
        return hash("MVar")
    
    @override
    def get_num_fvars(self): 
        return 0
    
    @override
    def get_num_bvars(self): 
        return 0
    
    @override
    def get_bvar_range(self): 
        return -1
    
    @override
    def get_num_expr_mvars(self): 
        return 1
    
    @override
    def get_lvl_mvars(self): 
        return 0
    
    @override
    def get_expr_size(self) -> int: 
        return 1
    
    @override
    def __str__(self) -> str: 
        return "MVar"

expr_constructors = [BVar, FVar, Sort, Const, App, Pi, Lambda, Let, Proj, NatLit, StrLit]

__all__ = ['Expression', 'BVar', 'FVar', 'Sort', 'Const', 'App', 'Pi', 'Lambda', 'Let', 'Proj', 'NatLit', 'StrLit', 'MVar', 'expr_constructors']