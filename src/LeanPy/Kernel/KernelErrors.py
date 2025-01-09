from typing import Type
from LeanPy.Structures.Environment.LocalContext import LocalContext
from LeanPy.Structures.Expression.Expression import Expression

""" 
Three classes of errors are defined here:
 - PanicError: This error is thrown when something that should never happen happens: reaching cases that should be unreachable, etc.    
 - KernelError: This error is thrown when the kernel operated correctly but the input was incorrect therefore the expression  is not well-typed.
 - UnfinishedError: This error is thrown when the kernel operated correctly, the expression was well-typed up to the point the kernel encountered an unfinished expression.
"""

# Panic Errors
class PanicError(Exception):
    def __init__(self, message : str):
        super().__init__(message)

# Kernel Errors
class KernelError(Exception):
    def __init__(self, message : str):
        self.message = message
        super().__init__(self.message)

class ExpectedDifferentExpressionError(KernelError):
    def __init__(self, expected : Type[Expression], got : Type[Expression]):
        super().__init__(f"Expected expression of type {expected.__name__} but got {got.__name__}")

class ExpectedDifferentTypesError(KernelError):
    def __init__(self, expected : Expression, got : Expression, local_context : LocalContext | None = None):
        super().__init__(f"Expected type\n\t{expected}\nbut got\n\t{got}" + (f"\nLocal context:\n{local_context}" if local_context is not None else ""))

class ProjectionError(KernelError):
    def __init__(self, message : str):
        super().__init__(message)

class EnvironmentError(KernelError):
    def __init__(self, message : str):
        super().__init__(message)

class DeclarationError(KernelError):
    def __init__(self, message : str):
        super().__init__(message)

class RecursorError(KernelError):
    def __init__(self, message : str):
        super().__init__(message)

class FoundUnsubstitutedBVarError(KernelError):
    def __init__(self):
        super().__init__("Found unsubstituted BVar")

# Unfinished Errors
class UnfinishedError(Exception):
    def __init__(self):
        super().__init__("Unfinished expression encountered")