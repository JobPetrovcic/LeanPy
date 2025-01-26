from Structures.Environment.LocalContext import LocalContext as LocalContext
from Structures.Expression.Expression import Expression as Expression
from _typeshed import Incomplete

class KernelError(Exception):
    message: Incomplete
    def __init__(self, message: str) -> None: ...

class PanicError(KernelError):
    def __init__(self, message: str) -> None: ...

class ExpectedDifferentExpressionError(KernelError):
    def __init__(self, expected: type[Expression], got: type[Expression]) -> None: ...

class ExpectedDifferentTypesError(KernelError):
    def __init__(self, expected: Expression, got: Expression, local_context: LocalContext | None = None) -> None: ...

class ProjectionError(KernelError):
    def __init__(self, message: str) -> None: ...

class EnvironmentError(KernelError):
    def __init__(self, message: str) -> None: ...

class DeclarationError(KernelError):
    def __init__(self, message: str) -> None: ...

class RecursorError(KernelError):
    def __init__(self, message: str) -> None: ...
