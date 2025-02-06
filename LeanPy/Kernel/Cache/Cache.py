from typing import Dict, Generic, Optional, Tuple, TypeVar
from LeanPy.Structures.Expression.ExpressionDebug import Expression

class MapCache:
    def __init__(self):
        # based on hashes and total equality (see Expression.__eq__)
        self.cache : Dict[Expression, Expression] = {} 
    
    def get(self, key : Expression) -> Optional[Expression]:
        return self.cache.get(key, None)
    
    def put(self, key : Expression, value : Expression):
        if key in self.cache:
            if self.cache[key] != value: raise Exception(f"MapCache already contains key {key} with different value (in terms of total equality) {self.cache[key]}")
            else: return # value is the same
        
        self.cache[key] = value
    
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
        self.cache: Dict[Tuple[N, M], T] = {}
    
    def get(self, expr1: N, expr2: M) -> Optional[T]:
        return self.cache.get((expr1, expr2), None)
    
    def put(self, expr1: N, expr2: M, value: T):
        key = (expr1, expr2)
        if key in self.cache:
            if self.cache[key] != value:
                raise Exception(f"PairCache already contains key {key} with different value {self.cache[key]}")
            return
        self.cache[key] = value
    
    def clear(self):
        self.cache.clear()