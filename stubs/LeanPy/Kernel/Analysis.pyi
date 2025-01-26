from Structures.Environment.LocalContext import LocalContext as LocalContext
from Structures.Expression.Expression import Expression as Expression
from typing import Any, Callable

def has_fvar_not_in_context(body: Expression, context: LocalContext): ...
def print_function_name(func: Callable[[Any], Any]) -> Callable[[Any], Any]: ...
def print_neg_verbose(fn: Callable[[Any, Expression, Expression], tuple[Expression, Expression, bool]]): ...
def print_neg(fn: Callable[[Any, Expression, Expression], bool]): ...
def dprint(s: str): ...

r_print: bool

def rprint(s: str): ...
