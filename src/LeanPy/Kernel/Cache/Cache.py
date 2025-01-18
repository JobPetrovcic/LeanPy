from typing import Dict, Generic, Optional, Tuple, TypeVar
from LeanPy.Structures.Expression.Expression import Expression

class MapCache:
    def __init__(self):
        # based on hashes and total equality (see Expression.__eq__ and Expression.totally_equal)
        self.cache : Dict[Tuple[Expression, int], Expression] = {} 
    
    def get(self, expr : Expression) -> Optional[Expression]:
        return self.cache.get((expr, expr.version), None)
    
    def put(self, expr : Expression, value : Expression):
        key = (expr, expr.version)
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
class PairCache(Generic[T]):
    """
    Cache objects for pairs of expressions, formally Expression x Expression -> T
    """
    def __init__(self):
        self.cache: Dict[Tuple[Tuple[Expression, int], Tuple[Expression, int]], T] = {}
    
    def get(self, expr1: Expression, expr2: Expression) -> Optional[T]:
        key1 = (expr1, expr1.version)
        key2 = (expr2, expr2.version)
        return self.cache.get((key1, key2), None)
    
    def put(self, expr1: Expression, expr2: Expression, value: T):
        key = ((expr1, expr1.version), (expr2, expr2.version))
        if key in self.cache:
            if self.cache[key] != value:
                raise Exception(f"PairCache already contains key {key} with different value {self.cache[key]}")
            return
        self.cache[key] = value
    
    def clear(self):
        self.cache.clear()