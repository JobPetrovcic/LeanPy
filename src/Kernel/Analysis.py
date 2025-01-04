from typing import Any, Callable, Tuple

from typeguard import typechecked

from Structures.Environment.LocalContext import LocalContext
from Structures.Expression.Expression import Expression, FVar
from Structures.Expression.ExpressionManipulation import do_fn

@typechecked
def has_fvar_not_in_context(body : Expression, context : LocalContext):
    """ Raises an error if the given expression contains a free variable not in the given context. """
    def fn(expr : Expression):
        if isinstance(expr, FVar) and expr not in context.fvars: raise ValueError(f"In body\n\t{body}\n\n found free variable\n\t{expr}\n\n not in context {context}")
    do_fn(body, fn)

def print_function_name(func : Callable[[Any], Any]) -> Callable[[Any], Any]:
    def wrapper(*args : Any, **kwargs : Any) -> Any:
        print(f"{func.__name__}")
        return func(*args, **kwargs)
    return wrapper

def print_neg_verbose(fn :Callable[[Any, Expression, Expression], Tuple[Expression, Expression, bool]]):
    def wrapper(self_arg : Any, l : Expression, r : Expression):
        l_n, r_n, result = fn(self_arg, l, r)
        if not result:
            print(f"l_n type was {self_arg.infer_core(l_n, infer_only=False)}")
            print(f"r_n type was {self_arg.infer_core(r_n, infer_only=False)}")
            print(f"Negative test failed for {fn.__name__} with\n\t{l_n}\nand\n\t{r_n}")
        return result
    return wrapper

def print_neg(fn :Callable[[Any, Expression, Expression], bool]):
    def wrapper(self_arg : Any, l : Expression, r : Expression):
        result = fn(self_arg, l, r)
        if not result:
            print(f"Negative test failed for {fn.__name__} with\n\t{l}\nand\n\t{r}")
        return result
    return wrapper

def dprint(s : str):
    print(s)

r_print : bool = True
def rprint(s : str):
    if r_print:
        print(s)