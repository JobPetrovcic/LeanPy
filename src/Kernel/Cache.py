from typing import Dict, Optional
from Structures.Expression.Expression import Expression

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