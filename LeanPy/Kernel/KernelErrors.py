from typing import Type
from LeanPy.Structures.Expression.Expression import Expression

should_print_expressions = False

# Fatal errors
class PanicError(Exception):
    def __init__(self, message : str):
        super().__init__(message)

class CacheError(Exception):
    def __init__(self, message : str):
        super().__init__(message)

class DeclarationError(Exception):
    def __init__(self, message : str):
        super().__init__(message)

# Kernel errors
class KernelError(Exception):
    def __init__(self, message : str):
        self.message = message
        super().__init__(self.message)

class ExpectedEqualExpressionsConstructorsError(KernelError):
    def __init__(self, expected : Type[Expression], got : Type[Expression]):
        super().__init__(f"Expected expression of type {expected.__name__} but got {got.__name__}")

class ExpectedEqualExpressionsError(KernelError):
    def __init__(self, expected : Expression, got : Expression):
        if should_print_expressions:
           super().__init__(f"Expected type\n\t{expected}\nbut got\n\t{got}")
        else:
            super().__init__(f"Expected types to be the same")

class ProjectionError(KernelError):
    def __init__(self, message : str):
        super().__init__(message)

class TCEnvironmentError(KernelError):
    def __init__(self, message : str):
        super().__init__(message)

class RecursorError(KernelError):
    def __init__(self, message : str):
        super().__init__(message)

class StructureError(KernelError):
    def __init__(self, message : str):
        super().__init__(message)

class UnboundVariableError(KernelError):
    def __init__(self, message : str):
        super().__init__(message)

class UnfinishedExpressionError(KernelError):
    def __init__(self, message : str):
        super().__init__(message)

class LocalContextError(KernelError):
    def __init__(self, message : str):
        super().__init__(message)

