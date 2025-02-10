import functools
from typing import Callable, Dict, Optional, List, Sequence, Tuple

from LeanPy.Structures.Expression.Level import *


from typeguard import typechecked
from LeanPy.Kernel.KernelErrors import PanicError
from LeanPy.Structures.Expression.Level import *
    
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

def is_not_zero(level : Level) -> bool:
    if isinstance(level, LevelZero) or isinstance(level, LevelParam):
        return False
    elif isinstance(level, LevelSucc):
        return True
    elif isinstance(level, LevelMax):
        return is_not_zero(level.lhs) or is_not_zero(level.rhs)
    elif isinstance(level, LevelIMax):
        return is_not_zero(level.rhs)
    raise PanicError("Unreachable code reached in is_not_zero")

def make_imax(l : Level, r : Level) -> Level:
    if is_not_zero(r):
        return make_max_pair(l, r)
    elif isinstance(r, LevelZero):
        return r
    elif isinstance(l, LevelZero):
        return r
    elif l.structurally_equal(r):
        return l
    else:
        return LevelIMax(l, r)

def push_max_args(l : Level, lst : List[Level]) -> None:
    if isinstance(l, LevelMax):
        push_max_args(l.lhs, lst)
        push_max_args(l.rhs, lst)
    else:
        lst.append(l)

lvl_class_to_int : Dict[type[Level], int]= {
    LevelZero: 0,
    LevelSucc: 1,
    LevelMax : 2,
    LevelIMax : 3,
    LevelParam : 4
}

def is_norm_lt(a : Level, b : Level) -> bool:
    if a is b: return False
    l1, o1 = to_offset(a)
    l2, o2 = to_offset(b)
    if l1.structurally_equal(l2): return o1 < o2

    if l1.__class__ != l2.__class__: return lvl_class_to_int[l1.__class__] < lvl_class_to_int[l2.__class__]

    if isinstance(l1, LevelZero) or isinstance(l1, LevelSucc): raise PanicError("Unreachable code reached in is_norm_lt")
    elif isinstance(l1, LevelParam) and isinstance(l2, LevelParam): return str(l1.pname) < str(l2.pname)
    elif (isinstance(l1, LevelMax) and isinstance(l2, LevelMax)) or (isinstance(l1, LevelIMax) and isinstance(l2, LevelIMax)):
        if l1.lhs.structurally_equal(l2.lhs): return is_norm_lt(l1.rhs, l2.rhs)
        else: return is_norm_lt(l1.lhs, l2.lhs)
    raise PanicError("Unreachable code reached in is_norm_lt")

def lt_compare(a : Level, b : Level) -> int:
    if is_norm_lt(a, b): return -1
    if is_norm_lt(b, a): return 1
    if not a.structurally_equal(b):
        raise PanicError("Unreachable code reached in lt_compare")
    return 0

key_lt = functools.cmp_to_key(lt_compare)

def is_explicit(l : Level) -> bool:
    r, _ = to_offset(l)
    return isinstance(r, LevelZero)

def make_max_pair(l1 : Level, l2 : Level) -> Level:
    if is_explicit(l1) and is_explicit(l2): return l1 if to_offset(l1)[1] >= to_offset(l2)[1] else l2
    elif l1.structurally_equal(l2): return l1
    elif isinstance(l1, LevelZero): return l2
    elif isinstance(l2, LevelZero): return l1
    elif isinstance(l2, LevelMax) and (l2.lhs.structurally_equal(l1) or l2.rhs.structurally_equal(l1)): return l2
    elif isinstance(l1, LevelMax) and (l1.lhs.structurally_equal(l2) or l1.rhs.structurally_equal(l2)): return l1
    else:
        p1 = to_offset(l1)
        p2 = to_offset(l2)
        if p1[0].structurally_equal(p2[0]):
            if p1[1] == p2[1]:
                raise PanicError("Unreachable code reached in make_max_pair")
            return l1 if p1[1] > p2[1] else l2
        else:
            return LevelMax(l1, l2)

def make_max(args : List[Level]) -> Level:
    if len(args) == 0: raise PanicError("Empty list passed to make_max")
    if len(args) == 1: return args[0]
    cur = make_max_pair(args[-2], args[-1])
    for i in range(len(args) - 3, -1, -1):
        cur = make_max_pair(args[i], cur)
    return cur

def normalize(l : Level) -> Level:
    r, offset = to_offset(l)
    if isinstance(r, LevelSucc): raise PanicError("Unreachable code reached in normalize")
    elif isinstance(r, LevelZero) or isinstance(r, LevelParam): return l
    elif isinstance(r, LevelIMax):
        im = make_imax(normalize(r.lhs), normalize(r.rhs))
        if not isinstance(im, LevelIMax): return normalize(from_offset(im, offset)) # this is not in the original code and I am unsure why not
        return from_offset(im, offset)
    elif isinstance(r, LevelMax):
        todo : List[Level] = []
        args : List[Level] = []
        push_max_args(r, todo)
        for a in todo:
            push_max_args(normalize(a), args)

        args.sort(key=key_lt)

        rargs : List[Level] = []
        i = 0 # the largest current levle
        if is_explicit(args[i]):
            while i + 1 < len(args) and is_explicit(args[i + 1]): # get the largest explicit level
                i += 1
            k = to_offset(args[i])[1]
            j = i + 1
            while j < len(args):
                if to_offset(args[j])[1] >= k: # if there is a level with a larger offset but not necessarily explicit we save it
                    break
                j += 1
            if j < len(args): # if we found a level with a larger offset we save it
                i += 1
        rargs.append(args[i])
    
        pp = to_offset(args[i]) # the largest current level
        i += 1
        for i in range(i, len(args)):
            q = to_offset(args[i])
            if pp[0].structurally_equal(q[0]):
                if pp[1] < q[1]:
                    pp = q # if we found a larger one we save it
                    rargs.pop()
                    rargs.append(args[i])
            else:
                pp = q
                rargs.append(args[i])
        
        for i in range(len(rargs)):
            rargs[i] = from_offset(rargs[i], offset)
        ret = make_max(rargs)
        return ret
    raise PanicError("Unreachable code reached in normalize")

def are_unique_level_params(levels : Sequence[Level]) -> bool:
    """Checks if all elements in the list are unique levels."""
    sorted_levels = sorted(levels, key=key_lt)
    
    for i in range(len(sorted_levels) - 1):
        if lt_compare(sorted_levels[i], sorted_levels[i + 1]) == 0:
            return False
    return True

@typechecked
def is_any_max(level : Level) -> bool:
    return isinstance(level, LevelMax) or isinstance(level, LevelIMax)

def is_equivalent(l : Level, r : Level) -> bool:
    return (l is r) or l.structurally_equal(r) or normalize(l).structurally_equal(normalize(r)) # TODO: should we cache

def is_equivalent_list(l : List[Level], r : List[Level]) -> bool:
    if len(l) != len(r): return False
    for i in range(len(l)):
        if not is_equivalent(l[i], r[i]): 
            return False
    return True

def replace_level(level : Level, fn : Callable[[Level], Optional[Level]]) -> Level:
    """ 
    Recursively replaces sublevels in the given level using the given function. It does by creating a new level tree for levels that refer to other levels.
    """
    new_level = fn(level)
    if new_level is not None: return new_level

    if isinstance(level, LevelZero): return level # does not refer to any other level
    elif isinstance(level, LevelParam): return level # does not refer to any other level
    elif isinstance(level, LevelSucc): return LevelSucc(replace_level(level.anc, fn))
    elif isinstance(level, LevelMax): return LevelMax(replace_level(level.lhs, fn), replace_level(level.rhs, fn))
    elif isinstance(level, LevelIMax): return LevelIMax(replace_level(level.lhs, fn), replace_level(level.rhs, fn))
    else: raise PanicError(f"Unknown level type {level.__class__.__name__}")

LevelSubList = List[Tuple[LevelParam, Level]]

def substitute_level_params_level(level : Level, params : LevelSubList) -> Level:
    """ Replaces all level parameters in the given level with the given values. """
    def replace_fn(l : Level) -> Optional[Level]:
        for to_sub, value in params:
            if isinstance(l, LevelParam) and l.pname == to_sub.pname:
                return value
        return None
    return replace_level(level, replace_fn)

__all__ = ["are_unique_level_params", "is_equivalent", "is_equivalent_list", "make_imax"]