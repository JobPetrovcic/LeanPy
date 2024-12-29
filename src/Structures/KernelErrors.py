from typing import Type
from Structures.Expression.Expression import Expression


class KernelError(Exception):
    def __init__(self, message : str):
        self.message = message
        super().__init__(self.message)

class PanicError(KernelError):
    def __init__(self, message : str):
        super().__init__(message)

class ExpectedDifferentExpressionError(KernelError):
    def __init__(self, expected : Type[Expression], got : Type[Expression]):
        super().__init__(f"Expected expression of type {expected.__name__} but got {got.__name__}")

class ExpectedDifferentTypesError(KernelError):
    def __init__(self, expected : Expression, got : Expression):
        super().__init__(f"Expected type\n\t{expected}\nbut got\n\t{got}")

class ProjectionError(KernelError):
    def __init__(self, message : str):
        super().__init__(message)

class EnvironmentError(KernelError):
    def __init__(self, message : str):
        super().__init__(message)

class DeclarationError(KernelError):
    def __init__(self, message : str):
        super().__init__(message)