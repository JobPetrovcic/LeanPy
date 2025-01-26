from typing import Dict, Optional

from LeanPy.Structures.Expression.Expression import Expression

class DSUObject:
    def __init__(self, _parent : Optional['DSUObject'] = None):
        self._parent = _parent
        self._rank = 0
    
    def get_root(self) -> 'DSUObject':
        if self._parent is None:
            return self
        self._parent = self._parent.get_root()
        return self._parent
    
    def join(self, other : 'DSUObject'):
        root1 = self.get_root()
        root2 = other.get_root()
        if root1 == root2: return
        if root1._rank < root2._rank:
            root1, root2 = root2, root1
        root2._parent = root1

        if root1._rank == root2._rank:
            root1._rank += 1

class EquivManager:
    def __init__(self):
        self.expr_to_dsu : Dict[Expression, DSUObject] = {}
    
    def were_found_and_equiv(self, expr1 : Expression, expr2 : Expression) -> bool:
        if expr1 not in self.expr_to_dsu: return False
        if expr2 not in self.expr_to_dsu: return False
        return self.expr_to_dsu[expr1].get_root() == self.expr_to_dsu[expr2].get_root()
    
    def add_equiv(self, expr1 : Expression, expr2 : Expression):
        if expr1 not in self.expr_to_dsu:
            self.expr_to_dsu[expr1] = DSUObject()
        if expr2 not in self.expr_to_dsu:
            self.expr_to_dsu[expr2] = DSUObject()
        self.expr_to_dsu[expr1].join(self.expr_to_dsu[expr2])
        