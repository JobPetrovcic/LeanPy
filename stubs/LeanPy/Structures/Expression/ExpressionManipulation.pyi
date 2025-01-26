from Structures.Expression.Expression import *
from Structures.Expression.Level import Level as Level, LevelParam as LevelParam
from Structures.Expression.LevelManipulation import LevelSubList as LevelSubList
from enum import Enum
from typing import Callable, Sequence

def replace_expression(expr: Expression, fn: Callable[[Expression], Expression | None]) -> Expression: ...
def replace_expression_w_depth(expr: Expression, fn: Callable[[Expression, int], Expression | None], depth: int) -> Expression: ...
def do_fn(expr: Expression, fn: Callable[[Expression], None]): ...
def do_fn_w_depth(expr: Expression, fn: Callable[[Expression, int], None], depth: int): ...
def substitute_level_params_in_expression(body: Expression, params: LevelSubList) -> Expression: ...
def instantiate_bvar(body: Expression, val: Expression) -> Expression: ...
def instantiate_bvars(body: Expression, vals: Sequence[Expression]) -> Expression: ...
def abstract_bvar(body: Expression, fvar: FVar) -> Expression: ...
def abstract_multiple_bvar(fvars: list[FVar], body: Expression) -> Expression: ...
def unfold_app(expr: Expression) -> tuple[Expression, list[Expression]]: ...
def unfold_app_rev(expr: Expression) -> tuple[Expression, list[Expression]]: ...
def get_app_function(expr: Expression) -> Expression: ...
def fold_apps(fn: Expression, args: list[Expression]) -> Expression: ...
def has_specific_fvar(expr: Expression, fvar: FVar) -> bool: ...
def has_fvar(expr: Expression) -> bool: ...
def level_zip(lvl_params: list[LevelParam], lvl_values: list[Level]) -> LevelSubList: ...
def get_binding_type(expr: Expression) -> Expression: ...
def get_binding_body(expr: Expression) -> Expression: ...
def has_loose_bvars(expr: Expression) -> bool: ...

class ReductionStatus(Enum):
    NOT_EQUAL = 0
    EQUAL = 1
    CONTINUE = 2
    UNKNOWN = 3
