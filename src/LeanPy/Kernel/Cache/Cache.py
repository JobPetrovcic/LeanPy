from typing import Dict, Generic, Optional, Tuple, TypeVar
from LeanPy.Structures.Expression.Expression import Expression

class MapCache:
    def __init__(self):
        # based on hashes and total equality (see Expression.__eq__ and Expression.totally_equal)
        self.cache : Dict[Expression, Expression] = {} 
    
    def get(self, key : Expression) -> Optional[Expression]:
        return self.cache.get(key, None)
    
    def put(self, key : Expression, value : Expression):
        if key in self.cache:
            if self.cache[key] != value: raise Exception(f"MapCache already contains key {key} with different value (in terms of total equality) {self.cache[key]}")
            else: return # value is the same
        
        self.cache[key] = value

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
        self.cache: Dict[Tuple[Expression, Expression], T] = {}
    
    def get(self, expr1: Expression, expr2: Expression) -> Optional[T]:
        return self.cache.get((expr1, expr2), None)
    
    def put(self, expr1: Expression, expr2: Expression, value: T):
        key = (expr1, expr2)
        if key in self.cache:
            if self.cache[key] != value:
                raise Exception(f"PairCache already contains key {key} with different value {self.cache[key]}")
            return
        self.cache[key] = value