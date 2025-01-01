from typing import Any, Callable


def print_function_name(func : Callable) -> Callable:
    def wrapper(*args : Any, **kwargs : Any) -> Any:
        print(f"{func.__name__}")
        return func(*args, **kwargs)
    return wrapper