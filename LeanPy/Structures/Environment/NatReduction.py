from typing import Callable, Optional

from LeanPy.Kernel.KernelErrors import DeclarationError
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
def nat_mod(a : int, b : int) -> int: return a if b == 0 else a % b
def nat_div(a : int, b : int) -> int: return 0 if b == 0 else a // b
def nat_beq(a : int, b : int) -> bool: return a == b
def nat_ble(a : int, b : int) -> bool: return a <= b
def nat_land(a : int, b : int) -> int: return a & b
def nat_lor(a : int, b : int) -> int: return a | b
def nat_xor(a : int, b : int) -> int: return a ^ b
def nat_shiftl(a : int, b : int) -> int:return a << b
def nat_shiftr(a : int, b : int) -> int:return a >> b
def reduce_bin_nat_op(op : Callable[[int, int], int], arg1 : int, arg2 : int, source : Expression) -> NatLit: return NatLit(op(arg1, arg2), source=source.source)
def reduce_bin_nat_pred(environment : Environment, op : Callable[[int, int], bool], arg1 : int, arg2 : int, source : Expression) -> Expression: 
    if op(arg1, arg2): return Const(cname=environment.Bool_true_name, lvl_params=[], source=source.source)
    else: return Const(cname=environment.Bool_false_name, lvl_params=[], source=source.source)

def nat_lit_to_constructor(environment : Environment, nat_lit : NatLit) -> Expression:
    """ Returns the constructor form of the given natural literal. """
    if nat_lit.val == 0: return Const(cname=environment.Nat_zero_name, lvl_params=[], source=nat_lit.source)
    return App(
        Const(cname=environment.Nat_succ_name, lvl_params=[], source=nat_lit.source),
        NatLit(nat_lit.val-1, source=nat_lit.source),
        source=nat_lit.source
    )

def char_to_expression(environment : Environment, c : str, source : Expression) -> Expression:
    return App(
        Const(cname=environment.Char_name, lvl_params=[], source=source.source),
        NatLit(ord(c), source=source.source),
        source=source.source
    )

def get_char_list_nil_const(environment : Environment, source : Expression) -> Expression:
    return App(
        Const(cname=environment.List_nil_name, lvl_params=[environment.level_zero], source=source.source),
        Const(cname=environment.Char_name, lvl_params=[], source=source.source),
        source=source.source
    )

def get_char_list_cons_app(environment : Environment, c : str, tail : Expression, source : Expression):
    return App(
        App(
            App(
                Const(cname=environment.List_cons_name, lvl_params=[environment.level_zero], source=source.source),
                Const(cname=environment.Char_name, lvl_params=[], source=source.source),
                source=source.source
            ),
            char_to_expression(environment, c, source=source.source),
            source=source.source
        ),
        tail,
        source=source.source
    )

def str_to_char_list(environment : Environment, s : str, source : Expression) -> Expression:
    l = get_char_list_nil_const(environment, source=source.source)
    for c in s[::-1]:
        l = get_char_list_cons_app(environment, c, l, source=source.source)
    return l

def str_lit_to_constructor(environment : Environment, s : StrLit) -> Expression:
    char_list = str_to_char_list(environment, s.val, source=s.source)
    return App(
        Const(cname=environment.String_mk_name, lvl_params=[], source=s.source),
        char_list,
        source=s.source
    )

def is_nat_zero_const(environment : Environment, t : Expression) -> bool:
    if isinstance(t, Const) and t.cname == environment.Nat_zero_name:
        if len(t.lvl_params) != 0:
            raise DeclarationError(f"Expected 0 level parameters for Nat.zero, got {len(t.lvl_params)}.")
        return True
    return False

def is_nat_succ_const(environment : Environment, t : Expression) -> bool:
    if isinstance(t, Const) and t.cname == environment.Nat_succ_name:
        if len(t.lvl_params) != 0:
            raise DeclarationError(f"Expected 0 level parameters for Nat.succ, got {len(t.lvl_params)}.")
        return True
    return False

def is_nat_zero(environment : Environment, t : Expression) -> bool:
    return is_nat_zero_const(environment, t) or (isinstance(t, NatLit) and t.val == 0)

def is_nat_succ(environment : Environment, t : Expression) -> Optional[Expression]:
    if isinstance(t, NatLit):
        if t.val == 0: return None
        return NatLit(t.val-1, source=t.source)
    fn, apps, _ = unfold_app(t)
    if is_nat_succ_const(environment, fn) and len(apps) == 1:
        return apps[0]
    return None

__all__ = [
    'nat_add', 'nat_sub', 'nat_mul', 'nat_pow', 'nat_gcd', 'nat_mod', 'nat_div', 'nat_beq', 'nat_ble', 'nat_land', 'nat_lor', 'nat_xor', 'nat_shiftl', 'nat_shiftr',

    'reduce_bin_nat_op', 'reduce_bin_nat_pred',

    'nat_lit_to_constructor', 'str_lit_to_constructor'
]