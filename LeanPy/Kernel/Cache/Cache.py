from typing import Dict, Generic, List, Optional, Tuple, TypeVar
from LeanPy.Kernel.KernelErrors import CacheError
from LeanPy.Structures.Expression.Expression import Expression

class MapCache:
    def __init__(self):
        # based on hashes and total equality (see Expression.__eq__)
        self.cache : Dict[int, Expression] = {} 
        self.cached_exprs : List[Expression] = []
    
    def get(self, expr : Expression) -> Optional[Expression]:
        return self.cache.get(id(expr), None)
    
    def put(self, expr : Expression, value : Expression):
        assert not expr.has_expr_mvars, f"Cannot cache expression with metavariables"
        assert not value.has_expr_mvars, f"Cannot cache expression with metavariables"
        key_id = id(expr)
        if key_id in self.cache:
            if self.cache[key_id] != value: 
                raise CacheError(f"MapCache already contains key {key_id} with different value (in terms of total equality) {self.cache[key_id]}")
            else: 
                return # value is the same
        
        self.cache[key_id] = value
        self.cached_exprs.append(expr) # save a reference to the expression so that it is not garbage collected
    
    def clear(self):
        self.cache.clear()
        self.cached_exprs.clear()

class InferCache(MapCache):
    def __init__(self):
        super().__init__()

class WHNFCache(MapCache):
    def __init__(self):
        super().__init__()


T = TypeVar("T")
N = TypeVar("N")
M = TypeVar("M")
class PairCache(Generic[N, M, T]):
    """
    Cache objects for pairs of expressions, formally Expression x Expression -> T
    """
    def __init__(self):
        self.cache: Dict[Tuple[int, int], T] = {}
        self.cached_exprs1: List[N] = []
        self.cached_exprs2: List[M] = []
    
    def get(self, expr1: N, expr2: M) -> Optional[T]:
        key_ids = (id(expr1), id(expr2))
        return self.cache.get(key_ids, None)
    
    def put(self, expr1: N, expr2: M, value: T):
        key = (id(expr1), id(expr2))
        if key in self.cache:
            if self.cache[key] != value:
                raise CacheError(f"PairCache already contains key {key} with different value {self.cache[key]}")
            return
        self.cache[key] = value
        self.cached_exprs1.append(expr1)
        self.cached_exprs2.append(expr2)
    
    def clear(self):
        self.cache.clear()
        self.cached_exprs1.clear()
        self.cached_exprs2.clear()