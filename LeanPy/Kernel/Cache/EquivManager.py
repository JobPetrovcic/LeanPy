from typing import Dict, Optional, Set, Tuple

from LeanPy.Structures.Expression.Expression import Expression

class DSUObject:
    def __init__(self, parent : Optional['DSUObject'] = None):
        self.parent = parent
        self.rank = 0
    
    def get_root(self) -> 'DSUObject':
        if self.parent is None:
            return self
        self.parent = self.parent.get_root()
        return self.parent
    
    def is_root(self) -> bool:
        return self.parent is None

class EquivManager:
    def __init__(self):
        self.expr_to_dsu : Dict[int, DSUObject] = {}

    def create_fresh_dsu_object(self, expr : Expression):
        key = id(expr)
        self.expr_to_dsu[key] = DSUObject()
        return self.expr_to_dsu[key]

    def expr_to_dsu_root(self, expr : Expression) -> DSUObject:
        key = id(expr)
        if key not in self.expr_to_dsu: return self.create_fresh_dsu_object(expr) # if the expression is not in the DSU, create a new DSU object, already in the root
        return self.expr_to_dsu[key].get_root() # get the root of the DSU object
    
    def add_equiv(self, expr1_dsu_root : DSUObject, expr2_dsu_root : DSUObject):
        if expr1_dsu_root == expr2_dsu_root: return
        if expr1_dsu_root.rank < expr2_dsu_root.rank:
            expr1_dsu_root, expr2_dsu_root = expr2_dsu_root, expr1_dsu_root
        expr2_dsu_root.parent = expr1_dsu_root

        if expr1_dsu_root.rank == expr2_dsu_root.rank:
            expr1_dsu_root.rank += 1

    def add_equiv_expressions(self, expr1 : Expression, expr2 : Expression):
        self.add_equiv(self.expr_to_dsu_root(expr1), self.expr_to_dsu_root(expr2))
        
    def clear(self):
        self.expr_to_dsu.clear()
        
class FailureCache:
    def __init__(self):
        self.did_fail : Set[Tuple[int, int]] = set()

    def put(self, expr1 : Expression, expr2 : Expression):
        key = (id(expr1), id(expr2))
        self.did_fail.add(key)
    
    def did_fail_before(self, expr1 : Expression, expr2 : Expression) -> bool:
        key = (id(expr1), id(expr2))
        return key in self.did_fail
    
    def clear(self):
        self.did_fail.clear()
    