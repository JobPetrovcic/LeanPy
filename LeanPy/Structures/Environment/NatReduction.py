from typing import Callable, Optional

from LeanPy.Structures.Environment.Environment import Environment
from LeanPy.Structures.Expression.Expression import App, Const, Expression, NatLit, StrLit
from LeanPy.Structures.Expression.ExpressionManipulation import unfold_app
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

def nat_lit_to_constructor(environment : Environment, nat_lit : NatLit) -> Expression:
    """ Returns the constructor form of the given natural literal. """
    if nat_lit.val == 0: return Const(cname=environment.Nat_zero_name, lvl_params=[])
    return App(
        Const(cname=environment.Nat_succ_name, lvl_params=[]),
        NatLit(nat_lit.val-1)
    )

def char_to_expression(environment : Environment, c : str) -> Expression:
    return App(
        Const(cname=environment.Char_name, lvl_params=[]),
        NatLit(ord(c))
    )

def get_char_list_nil_const(environment : Environment):
    return App(
        Const(cname=environment.List_nil_name, lvl_params=[environment.level_zero]),
        Const(cname=environment.Char_name, lvl_params=[])
    )

def get_char_list_cons_app(environment : Environment, c : str, tail : Expression):
    return App(
        App(
            App(
                Const(cname=environment.List_cons_name, lvl_params=[environment.level_zero]),
                Const(cname=environment.Char_name, lvl_params=[])
            ),
            char_to_expression(environment, c)
        ),
        tail
    )

def str_to_char_list(environment : Environment, s : str) -> Expression:
    l = get_char_list_nil_const(environment)
    for c in s[::-1]:
        l = get_char_list_cons_app(environment, c, l)
    print(l)
    return l

def str_lit_to_constructor(environment : Environment, s : StrLit) -> Expression:
    char_list = str_to_char_list(environment, s.val)
    return App(
        Const(cname=environment.String_mk_name, lvl_params=[]),
        char_list
    )

def is_nat_zero_const(environment : Environment, t : Expression) -> bool:
    if isinstance(t, Const) and t.cname == environment.Nat_zero_name:
        assert len(t.lvl_params) == 0, f"Expected 0 level parameters for Nat.zero, got {len(t.lvl_params)}."
        return True
    return False

def is_nat_succ_const(environment : Environment, t : Expression) -> bool:
    if isinstance(t, Const) and t.cname == environment.Nat_succ_name:
        assert len(t.lvl_params) == 0, f"Expected 0 level parameters for Nat.succ, got {len(t.lvl_params)}."
        return True
    return False

def is_nat_zero(environment : Environment, t : Expression) -> bool:
    return is_nat_zero_const(environment, t) or (isinstance(t, NatLit) and t.val == 0)

def is_nat_succ(environment : Environment, t : Expression) -> Optional[Expression]:
    if isinstance(t, NatLit):
        if t.val == 0: return None
        return NatLit(t.val-1)
    fn, apps = unfold_app(t)
    if is_nat_succ_const(environment, fn) and len(apps) == 1:
        return apps[0]
    return None

__all__ = [
    'nat_add', 'nat_sub', 'nat_mul', 'nat_pow', 'nat_gcd', 'nat_mod', 'nat_div', 'nat_beq', 'nat_ble', 'nat_land', 'nat_lor', 'nat_xor', 'nat_shiftl', 'nat_shiftr',

    'reduce_bin_nat_op', 'reduce_bin_nat_pred',

    'nat_lit_to_constructor', 'str_lit_to_constructor'
]