import sys
from typing import Any, Callable, Concatenate, ParamSpec, Tuple, TypeVar

from LeanPy.Structures.Expression.Expression import Expression
from line_profiler import LineProfiler

lp = LineProfiler()
T = TypeVar("T")
P = ParamSpec("P")

def profile(func : Callable[P, T]) -> Callable[P, T]:
    lp.add_function(func) # type: ignore
    return func  

def print_function_name(func: Callable[P, T]) -> Callable[P, T]:
    def wrapper(*args: P.args, **kwargs: P.kwargs) -> T:
        print(f"{func.__name__}")
        return func(*args, **kwargs)
    return wrapper

def err_print_neg_reduction(fn :Callable[[Any, Expression, Expression], Tuple[Expression, Expression, bool]]):
    def wrapper(self_arg : Any, l : Expression, r : Expression):
        l_n, r_n, result = fn(self_arg, l, r)
        if not result:
            print(f"l_n type was {self_arg.infer_core(l_n, infer_only=False)}", file=sys.stderr)
            print(f"r_n type was {self_arg.infer_core(r_n, infer_only=False)}", file=sys.stderr)
            print(f"Negative test failed for {fn.__name__} with\n\t{l_n}\nand\n\t{r_n}", file=sys.stderr)
        return result
    return wrapper

verbose = False
def err_print_neg(fn :Callable[[Any, Expression, Expression], bool]):
    def wrapper(self_arg : Any, l : Expression, r : Expression):
        result = fn(self_arg, l, r)
        if not result:
            print(f"Negative test failed for {fn.__name__} with\n\t{l}\nand\n\t{r}", file=sys.stderr)
            if verbose:
                print(f"the reduced expressions are \n\t{self_arg.whnf(l)}\nand\n\t{self_arg.whnf(r)}", file=sys.stderr)
                print(f"The types of the expressions are \n\t{self_arg.infer_core(l, infer_only=False)}\nand\n\t{self_arg.infer_core(r, infer_only=False)}", file=sys.stderr)
        return result
    return wrapper

monitor_expr = "(@List.length.{u_1} α (@List.cons.{u_1} α w___Init_Data_List_Lemmas__hyg_898 (@List.nil.{u_1} α)))"
def monitor_whnf(fn : Callable[Concatenate[Any, Expression, P], Expression]):
    def wrapper(self_arg : Any, expr : Expression, *args : P.args, **kwargs : P.kwargs):
        if str(expr) == monitor_expr:
            lp.enable() # type: ignore
            print("Enabled")
        
        result = fn(self_arg, expr, *args, **kwargs)

        if str(expr) == monitor_expr:
            lp.disable() # type: ignore
            lp.print_stats()
            #print(result)
            print("Disabled")
        return result
    return wrapper