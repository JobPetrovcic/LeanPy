from typing import Type
from LeanPy.Structures.Environment.LocalContext import LocalContext
from LeanPy.Structures.Expression.Expression import Expression

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
    def __init__(self, message : str, source : Expression):
        assert source.source is source, "KernelError source must be a source expression"
        self.message = message
        super().__init__(self.message)

class ExpectedEqualExpressionsConstructorsError(KernelError):
    def __init__(self, expected : Type[Expression], got : Type[Expression], source : Expression):
        super().__init__(f"Expected expression of type {expected.__name__} but got {got.__name__}", source)

class ExpectedEqualExpressionsError(KernelError):
    def __init__(self, expected : Expression, got : Expression, source : Expression, local_context : LocalContext | None = None):
        super().__init__(f"Expected type\n\t{expected}\nbut got\n\t{got}" + (f"\nLocal context:\n{local_context}" if local_context is not None else ""), source)

class ProjectionError(KernelError):
    def __init__(self, message : str, source : Expression):
        super().__init__(message, source)

class TCEnvironmentError(KernelError):
    def __init__(self, message : str, source : Expression):
        super().__init__(message, source)

class RecursorError(KernelError):
    def __init__(self, message : str, source : Expression):
        super().__init__(message, source)

class StructureError(KernelError):
    def __init__(self, message : str, source : Expression):
        super().__init__(message, source)

class UnboundVariableError(KernelError):
    def __init__(self, message : str, source : Expression):
        super().__init__(message, source)

class UnfinishedExpressionError(KernelError):
    def __init__(self, message : str, source : Expression):
        super().__init__(message, source)

class LocalContextError(KernelError):
    def __init__(self, message : str, source : Expression, local_context : LocalContext):
        super().__init__(message, source)