from typing import Dict, Generic, Optional, Tuple, TypeVar
from LeanPy.Kernel.KernelErrors import CacheError
from LeanPy.Structures.Expression.Expression import Expression

class MapCache:
    def __init__(self):
        # based on hashes and total equality (see Expression.__eq__)
        self.cache : Dict[int, Expression] = {} 
    
    def get(self, key : Expression) -> Optional[Expression]:
        return self.cache.get(id(key), None)
    
    def put(self, key : Expression, value : Expression):
        key_id = id(key)
        if key_id in self.cache:
            if self.cache[key_id] != value: 
                raise CacheError(f"MapCache already contains key {key_id} with different value (in terms of total equality) {self.cache[key_id]}")
            else: 
                return # value is the same
        
        self.cache[key_id] = value
    
    def clear(self):
        self.cache.clear()

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
    
    def clear(self):
        self.cache.clear()