import functools
from typing import Callable, Optional, List, Sequence, Tuple

from Structures.Expression.Level import *


from typeguard import typechecked
from Structures.KernelErrors import PanicError
from Structures.Expression.Level import *

def combine_to_max(l : Level, r : Level) -> Level:
    if isinstance(l, LevelZero):
        return r
    elif isinstance(r, LevelZero):
        return l
    elif isinstance(l, LevelSucc) and isinstance(r, LevelSucc):
        return LevelSucc(combine_to_max(l.anc, r.anc))
    else:
        return LevelMax(l, r)
    
def to_offset(level : Level) -> Tuple[Level, int]:
    cur = level
    offset = 0
    while isinstance(cur, LevelSucc):
        offset += 1
        cur = cur.anc
    return (cur, offset)

def from_offset(level : Level, offset : int) -> Level:
    cur = level
    for _ in range(offset):
        cur = LevelSucc(cur)
    return cur

def simplify(level : Level) -> Level:
    """Simplifies a level."""
    if isinstance(level, LevelZero):
        return level
    elif isinstance(level, LevelParam):
        return level
    elif isinstance(level, LevelSucc):
        return LevelSucc(simplify(level.anc))
    elif isinstance(level, LevelMax):
        l = simplify(level.lhs)
        r = simplify(level.rhs)
        return combine_to_max(l, r)
    elif isinstance(level, LevelIMax):
        simplified_r = simplify(level.rhs)
        if isinstance(simplified_r, LevelZero):
            return simplified_r
        elif isinstance(simplified_r, LevelSucc):
            return combine_to_max(simplify(level.lhs), simplified_r)
        else:
            return LevelIMax(simplify(level.lhs), simplified_r)
    else: raise ValueError(f"Cannot simplify unknown level type {level.__class__.__name__}")

def are_unique_level_params(levels : Sequence[Level]) -> bool:
    """Checks if all elements in the list are unique levels."""
    # sort using leq
    sorted_levels = sorted(levels, key=functools.cmp_to_key(lambda l, r: 1 if leq(l, r) else -1))
    for i in range(len(sorted_levels) - 1):
        if leq(sorted_levels[i + 1], sorted_levels[i]):
            return False
    return True


@typechecked
def is_any_max(level : Level) -> bool:
    return isinstance(level, LevelMax) or isinstance(level, LevelIMax)

@typechecked
def leq_imax_by_cases(m : LevelParam, l : Level, r : Level, diff : int) -> bool:
    """ Tests whether l <= r regardless of m."""
    lhs_0 = substitute_level_params_level(l, [(m, LevelZero())], True)
    rhs_0 = substitute_level_params_level(r, [(m, LevelZero())], True)
    lhs_1 = substitute_level_params_level(l, [(m, LevelSucc(LevelZero()))], True)
    rhs_1 = substitute_level_params_level(r, [(m, LevelSucc(LevelZero()))], True)
    return leq_core(lhs_0, rhs_0, diff) and leq_core(lhs_1, rhs_1, diff)

@typechecked
def leq_core(l : Level, r : Level, diff : int) -> bool:
    """Core logic for less-than-or-equal comparison of levels."""
    if isinstance(l, LevelZero) and diff >=0: return True
    elif isinstance(r, LevelZero) and diff < 0: return False
    elif isinstance(l, LevelParam) and isinstance(r, LevelParam): return l.name == r.name and diff >= 0
    elif isinstance(l, LevelParam) and isinstance(r, LevelZero): return False
    elif isinstance(l, LevelZero) and isinstance(r, LevelParam): return diff >= 0
    
    # handle succ
    elif isinstance(l, LevelSucc): return leq_core(l.anc, r, diff - 1)
    elif isinstance(r, LevelSucc): return leq_core(l, r.anc, diff + 1)

    # handle l is max
    elif isinstance(l, LevelMax): return leq_core(l.lhs, r, diff) and leq_core(l.rhs, r, diff)

    elif (isinstance(l, LevelParam) or isinstance(l, LevelZero)) and isinstance(r, LevelMax): return leq_core(l, r.lhs, diff) or leq_core(l, r.rhs, diff)

    elif isinstance(l, LevelIMax) and isinstance(r, LevelIMax) and leq_core(l.lhs, r.lhs, 0) and leq_core(l.rhs, r.rhs, 0): return True
    elif isinstance(l, LevelIMax) and isinstance(l.rhs, LevelParam): return leq_imax_by_cases(l.rhs, l, r, diff)
    elif isinstance(r, LevelIMax) and isinstance(r.rhs, LevelParam): return leq_imax_by_cases(r.rhs, l, r, diff)
    elif isinstance(l, LevelIMax) and is_any_max(l.rhs):
        a = l.lhs
        b = l.rhs
        if isinstance(b, LevelIMax):
            x, y = b.lhs, b.rhs
            new_lhs = LevelIMax(a, y)
            new_rhs = LevelIMax(x, y)
            new_max = LevelMax(new_lhs, new_rhs)
            return leq_core(new_max, r, diff)
        elif isinstance(b, LevelMax):
            x, y = b.lhs, b.rhs
            new_lhs = LevelIMax(a, x)
            new_rhs = LevelIMax(a, y)
            new_max = simplify(LevelMax(new_lhs, new_rhs))
            return leq_core(new_max, r, diff)
        else: raise PanicError(f"Unreachable case when comparing levels: {l} and {r}")
    elif isinstance(r, LevelIMax) and is_any_max(r.rhs):
        x = r.lhs
        y = r.rhs
        if isinstance(y, LevelIMax):
            j, k = y.lhs, y.rhs
            new_lhs = LevelIMax(x, k)
            new_rhs = LevelIMax(j, k)
            new_max = LevelMax(new_lhs, new_rhs)
            return leq_core(l, new_max, diff)
        elif isinstance(y, LevelMax):
            new_lhs = LevelIMax(r.lhs, y.lhs)
            new_rhs = simplify(LevelMax(new_lhs, LevelIMax(r.lhs, y.rhs)))
            return leq_core(l, new_rhs, diff)
        else: raise PanicError(f"Unreachable case when comparing levels: {l} and {r}")
    else: raise PanicError(f"Unreachable case when comparing levels: {l} and {r}")

@typechecked
def leq(l : Level, r : Level) -> bool:
    """Checks if l is less than or equal to r."""
    l_prime = simplify(l)
    r_prime = simplify(r)
    return leq_core(l_prime, r_prime, 0)

def is_zero_level(level : Level) -> bool:
    """Checks if the given level is zero."""
    return leq(level, LevelZero())

@typechecked
def antisymm_eq(l : Level, r : Level) -> bool:
    """Checks if l is equal to r."""
    return leq(l, r) and leq(r, l)

@typechecked
def antisymm_eq_list(l : List[Level], r : List[Level]) -> bool:
    """Checks if two lists of levels are equal."""
    if len(l) != len(r):
        return False
    for i in range(len(l)):
        if not antisymm_eq(l[i], r[i]):
            return False
    return True

def replace_level(level : Level, fn : Callable[[Level], Optional[Level]]) -> Level:
    """ Recursively replaces sublevels in the given level using the given function. It does this in place when it can.
    
    Args:
        level: The level to replace sublevels in.
        fn: The function to use to replace sublevels. It should return None if the level should not be replaced.

    Returns:
        The level with sublevels replaced.
    """
    new_level = fn(level)
    if new_level is not None: return new_level

    if isinstance(level, LevelZero): return level
    elif isinstance(level, LevelParam): return level
    elif isinstance(level, LevelSucc):
        level.anc = replace_level(level.anc, fn)
    elif isinstance(level, LevelMax):
        level.lhs = replace_level(level.lhs, fn)
        level.rhs = replace_level(level.rhs, fn)
    elif isinstance(level, LevelIMax):
        level.lhs = replace_level(level.lhs, fn)
        level.rhs = replace_level(level.rhs, fn)
    else: raise ValueError(f"Unknown level type {level.__class__.__name__}")
    return level
    
def replace_level_clone(level : Level, fn : Callable[[Level], Optional[Level]]) -> Level:
    """ 
    Recursively replaces sublevels in the given level using the given function. It does by creating a new level tree. 

    Args:
        level: The level to replace sublevels in.
        fn: The function to use to replace sublevels. It should return None if the level should not be replaced.
    
    Returns:
        The new level with sublevels replaced.
    """
    new_level = fn(level)
    if new_level is not None: return new_level

    if isinstance(level, LevelZero): return LevelZero()
    elif isinstance(level, LevelParam): return LevelParam(level.name) # don't clone the name
    elif isinstance(level, LevelSucc): return LevelSucc(replace_level_clone(level.anc, fn))
    elif isinstance(level, LevelMax): return LevelMax(replace_level_clone(level.lhs, fn), replace_level_clone(level.rhs, fn))
    elif isinstance(level, LevelIMax): return LevelIMax(replace_level_clone(level.lhs, fn), replace_level_clone(level.rhs, fn))
    else: raise ValueError(f"Unknown level type {level.__class__.__name__}")

LevelSubList = List[Tuple[LevelParam, Level]]

def substitute_level_params_level(level : Level, params : LevelSubList, clone : bool) -> Level:
    """ Replaces all level parameters in the given level with the given values. """
    def replace_fn(l : Level) -> Optional[Level]:
        for to_sub, value in params:
            if isinstance(l, LevelParam) and l.name == to_sub.name:
                return value
        return None
    if clone:
        return replace_level_clone(level, replace_fn)
    else:
        return replace_level(level, replace_fn)

def clone_level(level : Level) -> Level:
    """ Clones the given level. """
    return replace_level_clone(level, lambda l: None)