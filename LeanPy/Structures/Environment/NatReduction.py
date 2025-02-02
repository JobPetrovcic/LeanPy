from typing import Callable

from typeguard import typechecked

from LeanPy.Structures.Environment.Environment import Environment
from LeanPy.Structures.Expression.Expression import App, Const, Expression, NatLit, StrLit
def nat_add(a : int, b : int) -> int: return a + b
def nat_sub(a : int, b : int) -> int: return max(0, a - b)
def nat_mul(a : int, b : int) -> int: return a * b
def nat_pow(a : int, b : int) -> int: return a ** b
def nat_gcd(a : int, b : int) -> int:
    while b:
        a, b = b, a % b
    return a
def nat_mod(a : int, b : int) -> int: return 0 if b == 0 else a % b
def nat_div(a : int, b : int) -> int: return 0 if b == 0 else a // b
def nat_beq(a : int, b : int) -> bool: return a == b
def nat_ble(a : int, b : int) -> bool: return a <= b
def nat_land(a : int, b : int) -> int: return a & b
def nat_lor(a : int, b : int) -> int: return a | b
def nat_xor(a : int, b : int) -> int: return a ^ b
def nat_shiftl(a : int, b : int) -> int:return a << b
def nat_shiftr(a : int, b : int) -> int:return a >> b
def reduce_bin_nat_op(op : Callable[[int, int], int], arg1 : int, arg2 : int) -> NatLit: return NatLit(op(arg1, arg2))
def reduce_bin_nat_pred(environment : Environment, op : Callable[[int, int], bool], arg1 : int, arg2 : int) -> Expression: 
    if op(arg1, arg2): return Const(cname=environment.Bool_true_name, lvl_params=[])
    else: return Const(cname=environment.Bool_false_name, lvl_params=[])

@typechecked
def nat_lit_to_constructor(environment : Environment, nat_lit : NatLit) -> Expression: # DOES NOT CHANGE ANYTHING
    """ Returns the constructor form of the given natural literal. """
    if nat_lit.val == 0: return Const(cname=environment.Nat_zero_name, lvl_params=[])
    return App(
        Const(cname=environment.Nat_succ_name, lvl_params=[]),
        NatLit(nat_lit.val-1)
    )

@typechecked
def char_to_expression(environment : Environment, c : str) -> Expression: # DOES NOT CHANGE ANYTHING
    return App(
        Const(cname=environment.Char_name, lvl_params=[]),
        NatLit(ord(c))
    )

@typechecked
def str_to_char_list(environment : Environment, s : str, ind : int = 0) -> Expression: # DOES NOT CHANGE ANYTHING
    assert ind >= 0, "Index must be non-negative when converting a string literal to a constructor."
    if ind == len(s): 
        return App(
            Const(cname=environment.List_nil_name, lvl_params=[environment.level_one]),
            Const(cname=environment.Char_name, lvl_params=[])
        )
    else:
        return  App(
            App(
                App(
                    Const(cname=environment.List_cons_name, lvl_params=[environment.level_one]),
                    Const(cname=environment.Char_name, lvl_params=[])
                ),
                char_to_expression(environment, s[ind])
            ),
            str_to_char_list(environment, s, ind+1)
        )

@typechecked
def str_lit_to_constructor(environment : Environment, s : StrLit) -> Expression: # DOES NOT CHANGE ANYTHING
    char_list = str_to_char_list(environment, s.val, 0)
    return App(
        Const(cname=environment.String_mk_name, lvl_params=[]),
        char_list
    )

__all__ = [
    'nat_add', 'nat_sub', 'nat_mul', 'nat_pow', 'nat_gcd', 'nat_mod', 'nat_div', 'nat_beq', 'nat_ble', 'nat_land', 'nat_lor', 'nat_xor', 'nat_shiftl', 'nat_shiftr',

    'reduce_bin_nat_op', 'reduce_bin_nat_pred',

    'nat_lit_to_constructor', 'str_lit_to_constructor'
    ]