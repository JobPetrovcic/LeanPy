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
        self.expr_to_dsu : Dict[Expression, DSUObject] = {}

    def create_fresh_dsu_object(self, expr : Expression):
        assert expr not in self.expr_to_dsu, f"Expression {expr} already in DSU" # TODO: remove this after testing
        self.expr_to_dsu[expr] = DSUObject()
        return self.expr_to_dsu[expr]

    def expr_to_dsu_root(self, expr : Expression) -> DSUObject:
        if expr not in self.expr_to_dsu: return self.create_fresh_dsu_object(expr) # if the expression is not in the DSU, create a new DSU object, already in the root
        return self.expr_to_dsu[expr].get_root() # get the root of the DSU object
    
    def add_equiv(self, expr1_dsu_root : DSUObject, expr2_dsu_root : DSUObject):
        assert expr1_dsu_root.is_root() and expr2_dsu_root.is_root() # TODO: remove this after testing

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
        self.did_fail : Set[Tuple[Expression, Expression]] = set()

    def put(self, expr1 : Expression, expr2 : Expression):
        self.did_fail.add((expr1, expr2))
    
    def did_fail_before(self, expr1 : Expression, expr2 : Expression) -> bool:
        return (expr1, expr2) in self.did_fail
    