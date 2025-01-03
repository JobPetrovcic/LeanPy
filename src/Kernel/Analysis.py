from typing import Any, Callable, Tuple

from Structures.Expression.Expression import Expression


def print_function_name(func : Callable[[Any], Any]) -> Callable[[Any], Any]:
    def wrapper(*args : Any, **kwargs : Any) -> Any:
        print(f"{func.__name__}")
        return func(*args, **kwargs)
    return wrapper

def print_neg(fn :Callable[[Any, Expression, Expression], Tuple[Expression, Expression, bool]]):
    def wrapper(self_arg : Any, l : Expression, r : Expression):
        l_n, r_n, result = fn(self_arg, l, r)
        if not result:
            print(f"l_n type was {self_arg.infer_core(l_n, infer_only=False)}")
            print(f"r_n type was {self_arg.infer_core(r_n, infer_only=False)}")
            print(f"Negative test failed for {fn.__name__} with\n\t{l_n}\nand\n\t{r_n}")
        return result
    return wrapper

def dprint(s : str):
    print(s)

r_print : bool = True
def rprint(s : str):
    if r_print:
        print(s)