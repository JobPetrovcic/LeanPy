from typing import Type
from LeanPy.Structures.Expression.Expression import Expression, MVar

should_print_expressions = True

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

class TCEnvironmentError(Exception):
    def __init__(self, message : str):
        super().__init__(message)

# Kernel errors
class KernelError(Exception):
    def __init__(self, message : str, source : Expression):
        assert source.source is source, "KernelError source must be a source expression"
        self.source = source
        self.message = message
        super().__init__(self.message)

class ExpectedEqualExpressionsConstructorsError(KernelError):
    def __init__(self, expected : Type[Expression], got : Type[Expression], source : Expression):
        super().__init__(f"Expected expression of type {expected.__name__} but got {got.__name__}", source)

class ExpectedEqualExpressionsError(KernelError):
    def __init__(self, expected : Expression, got : Expression, source : Expression):
        if should_print_expressions:
           super().__init__(f"Expected type\n\t{expected}\nbut got\n\t{got}", source)
        else:
            super().__init__(f"Expected types to be the same", source)

class ProjectionError(KernelError):
    def __init__(self, message : str, source : Expression):
        if should_print_expressions:
            super().__init__(message + f"\n\t{source}", source)
        else:
            super().__init__(message, source)

class InvalidDeclarationNameError(KernelError):
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

class LocalContextError(KernelError):
    def __init__(self, message : str, source : Expression):
        super().__init__(message, source)

class DefinitionalEqualityError(Exception):
    def __init__(self, l : Expression, r : Expression):
        if isinstance(l, MVar) or isinstance(r, MVar):
            raise PanicError("Don't use DefinitionalEqualityError with metavariables")
        

        self.l = l
        self.r = r
        if should_print_expressions:
            super().__init__(f"Definitional equality failed\n\t{l}\nand\n\t{r}")
        else:
            super().__init__(f"Definitional equality failed")


# Special error for unfinished expressions
class UnfinishedExpressionError(Exception):
    def __init__(self, source : Expression):
        super().__init__("Expression is unfinished, cannot continue", source)