from typing import Callable

from Structures.Expression.Expression import NatLit


def nat_add(a : int, b : int) -> int:
        return a + b

def nat_sub(a : int, b : int) -> int:
    return max(0, a - b)

def nat_mul(a : int, b : int) -> int:
    return a * b

def nat_pow(a : int, b : int) -> int:
    return a ** b

def nat_gcd(a : int, b : int) -> int:
    while b:
        a, b = b, a % b
    return a

def nat_mod(a : int, b : int) -> int:
    if b == 0: return 0
    return a % b

def nat_div(a : int, b : int) -> int:
    if b == 0: return 0
    return a // b

def nat_eq(a : int, b : int) -> bool:
    return a == b

def nat_le(a : int, b : int) -> bool:
    return a <= b

def nat_land(a : int, b : int) -> int:
    return a & b

def nat_lor(a : int, b : int) -> int:
    return a | b

def nat_lxor(a : int, b : int) -> int:
    return a ^ b

def nat_shiftl(a : int, b : int) -> int:
    return a << b

def nat_shiftr(a : int, b : int) -> int:
    return a >> b


def reduce_bin_nat_op(op : Callable[[int, int], int], arg1 : int, arg2 : int) -> NatLit:
    return NatLit(op(arg1, arg2))

__all__ = [
    'nat_add', 'nat_sub', 'nat_mul', 'nat_pow', 'nat_gcd', 'nat_mod', 'nat_div', 'nat_eq', 'nat_le', 'nat_land', 'nat_lor', 'nat_lxor', 'nat_shiftl', 'nat_shiftr',

    'reduce_bin_nat_op'
    ]