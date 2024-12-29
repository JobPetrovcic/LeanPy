from typing import Callable
from typeguard import typechecked
from Structures.Expression.Expression import Expression
from Structures.Expression.ExpressionManipulation import clone_expression

class ExpressionWrapper:
    @typechecked
    def __init__(self, e: Expression):
        self.e = e

    def clone(self):
        return ExpressionWrapper(clone_expression(self.e, use_same_fvars=True))
    
    def apply(self, fn : Callable[[Expression], Expression]):
        self.e = fn(self.e)