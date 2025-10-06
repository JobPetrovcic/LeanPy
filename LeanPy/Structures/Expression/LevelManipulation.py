import functools
from typing import Any, Callable, Dict, Optional, List, Sequence, Set, Tuple

from LeanPy.Structures.Expression.Level import *
from LeanPy.Structures.Expression.LevelErrors import DefinitionalEqualityLevelError, PanicLevelError, UnfinishedLevelError
from typeguard import typechecked

from LeanPy.Structures.Name import Name, string_to_name
    
def to_offset(level : Level) -> Tuple[Level, int, List[Level]]:
    cur = level
    offset = 0
    level_sources : List[Level] = []
    while isinstance(cur, LevelSucc):
        offset += 1
        level_sources.append(cur)
        cur = cur.anc
    assert len(level_sources) == offset
    return cur, offset, level_sources

def from_offset(level : Level, offset : int, level_sources : List[Any]) -> Level:
    cur = level
    assert len(level_sources) == offset
    for source in reversed(level_sources):
        cur = LevelSucc(cur, source=source)
    return cur

def structurally_equal(l : Level, r : Level, expect_true : bool) -> bool:
    if isinstance(l, LevelMVar):
        raise UnfinishedLevelError(l)
    if isinstance(r, LevelMVar):
        raise UnfinishedLevelError(r)
    
    if l.__class__ != r.__class__:
        if expect_true:
            raise DefinitionalEqualityLevelError(l, r)
        return False
    
    if isinstance(l, LevelZero) and isinstance(r, LevelZero):
        return True
    elif isinstance(l, LevelSucc) and isinstance(r, LevelSucc):
        return structurally_equal(l.anc, r.anc, expect_true)
    elif isinstance(l, LevelMax) and isinstance(r, LevelMax):
        ret = structurally_equal(l.lhs, r.lhs, expect_true) and structurally_equal(l.rhs, r.rhs, expect_true)
        if not ret and expect_true:
            raise DefinitionalEqualityLevelError(l, r)
        return ret
    elif isinstance(l, LevelIMax) and isinstance(r, LevelIMax):
        ret = structurally_equal(l.lhs, r.lhs, expect_true) and structurally_equal(l.rhs, r.rhs, expect_true)
        if not ret and expect_true:
            raise DefinitionalEqualityLevelError(l, r)
        return ret
    elif isinstance(l, LevelParam) and isinstance(r, LevelParam):
        ret = l.pname == r.pname
        if not ret and expect_true:
            raise DefinitionalEqualityLevelError(l, r)
        return ret
    else:
        raise DefinitionalEqualityLevelError(l, r)

def is_not_zero(level : Level) -> bool:
    if isinstance(level, LevelMVar):
        raise UnfinishedLevelError(level)

    if isinstance(level, LevelZero) or isinstance(level, LevelParam):
        return False
    elif isinstance(level, LevelSucc):
        return True
    elif isinstance(level, LevelMax):
        return is_not_zero(level.lhs) or is_not_zero(level.rhs)
    elif isinstance(level, LevelIMax):
        return is_not_zero(level.rhs)
    raise PanicLevelError("Unreachable code reached in is_not_zero")

def make_imax(l : Level, r : Level, source : Any) -> Level:
    if is_not_zero(r):
        return make_max_pair(l, r, source=source)
    elif isinstance(r, LevelZero):
        return r
    elif isinstance(l, LevelZero):
        return r
    elif structurally_equal(l, r, False):
        return l
    else:
        return LevelIMax(l, r, source=source)

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
    l1, o1, _s1 = to_offset(a)
    l2, o2, _s2 = to_offset(b)
    if structurally_equal(l1, l2, False): return o1 < o2

    if l1.__class__ != l2.__class__: return lvl_class_to_int[l1.__class__] < lvl_class_to_int[l2.__class__]

    if isinstance(l1, LevelZero) or isinstance(l1, LevelSucc): raise PanicLevelError("Unreachable code reached in is_norm_lt")
    elif isinstance(l1, LevelParam) and isinstance(l2, LevelParam): return str(l1.pname) < str(l2.pname)
    elif (isinstance(l1, LevelMax) and isinstance(l2, LevelMax)) or (isinstance(l1, LevelIMax) and isinstance(l2, LevelIMax)):
        if structurally_equal(l1.lhs, l2.lhs, False): return is_norm_lt(l1.rhs, l2.rhs)
        else: return is_norm_lt(l1.lhs, l2.lhs)
    raise PanicLevelError("Unreachable code reached in is_norm_lt")

def lt_compare(a : Level, b : Level) -> int:
    if is_norm_lt(a, b): return -1
    if is_norm_lt(b, a): return 1
    if not structurally_equal(a, b, True):
        raise PanicLevelError("Unreachable code reached in lt_compare")
    return 0

key_lt = functools.cmp_to_key(lt_compare)

def is_explicit(l : Level) -> bool:
    r, _, _ = to_offset(l)
    return isinstance(r, LevelZero)

def make_max_pair(l1 : Level, l2 : Level, source : Optional[Any]) -> Level:
    if is_explicit(l1) and is_explicit(l2): return l1 if to_offset(l1)[1] >= to_offset(l2)[1] else l2
    elif structurally_equal(l1, l2, False): return l1
    elif isinstance(l1, LevelZero): return l2
    elif isinstance(l2, LevelZero): return l1
    elif isinstance(l2, LevelMax) and (structurally_equal(l1, l2.lhs, False) or structurally_equal(l1, l2.rhs, False)): return l2
    elif isinstance(l1, LevelMax) and (structurally_equal(l1.lhs, l2, False) or structurally_equal(l1.rhs, l2, False)): return l1
    else:
        rp1, op1, _s1 = to_offset(l1)
        rp2, op2, _s2 = to_offset(l2)
        p1 = (rp1, op1)
        p2 = (rp2, op2)
        if structurally_equal(p1[0], p2[0], False):
            if p1[1] == p2[1]:
                raise PanicLevelError("Unreachable code reached in make_max_pair")
            return l1 if p1[1] > p2[1] else l2
        else:
            return LevelMax(l1, l2, source=source)

def make_max(args : List[Level], sources : List[Optional[Any]]) -> Level:
    assert len(args) - 1 == len(sources)
    if len(args) == 0: raise PanicLevelError("Empty list passed to make_max")
    if len(args) == 1: return args[0]
    cur = make_max_pair(args[-2], args[-1], source=sources[-1])
    for i in range(len(args) - 3, -1, -1):
        cur = make_max_pair(args[i], cur, source=sources[i])
    return cur

def normalize(l : Level) -> Level:
    r, offset, sources = to_offset(l)
    if isinstance(r, LevelSucc): raise PanicLevelError("Unreachable code reached in normalize")
    elif isinstance(r, LevelZero) or isinstance(r, LevelParam): return l
    elif isinstance(r, LevelIMax):
        im = make_imax(normalize(r.lhs), normalize(r.rhs), source=r.source)
        if not isinstance(im, LevelIMax): return normalize(from_offset(im, offset, sources)) # this is not in the original code and I am unsure why not
        return from_offset(im, offset, sources)
    elif isinstance(r, LevelMax):
        todo : List[Level] = []
        args : List[Level] = []
        push_max_args(r, todo)
        for a in todo:
            push_max_args(normalize(a), args)

        args.sort(key=key_lt)

        rargs : List[Level] = []
        i = 0 # the largest current level
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
    
        rpp, opp, _pp_sources = to_offset(args[i]) # the largest current level
        pp = (rpp, opp)
        i += 1
        for i in range(i, len(args)):
            rq, oq, _q_sources = to_offset(args[i])
            q = (rq, oq)
            if structurally_equal(pp[0], q[0], False): # the "remaining" levels are the same
                if pp[1] < q[1]: # if the offset is larger
                    pp = q # we save it
                    rargs.pop()
                    rargs.append(args[i])
            else:
                pp = q
                rargs.append(args[i])
        
        for i in range(len(rargs)):
            rargs[i] = from_offset(rargs[i], offset, sources) # add back the initial offset
        ret = make_max(rargs, [l.source] * (len(rargs) - 1))
        return ret
    elif isinstance(r, LevelMVar):
        return l # nothing to normalize
    raise PanicLevelError("Unreachable code reached in normalize")

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

def is_equivalent(l : Level, r : Level, expect_true : bool) -> bool:
    return (l is r) or structurally_equal(l, r, False) or structurally_equal(normalize(l), normalize(r), expect_true) # TODO: should we cache

def is_equivalent_list(l : List[Level], r : List[Level], expect_true : bool) -> bool:
    if len(l) != len(r): return False
    for i in range(len(l)):
        if not is_equivalent(l[i], r[i], expect_true): 
            if expect_true:
                raise PanicLevelError("This should be unreachable")
            return False
    return True

def replace_level(level : Level, fn : Callable[[Level], Optional[Level]], replace_source : Optional[Any]) -> Level:
    """ 
    Recursively replaces sublevels in the given level using the given function. It does by creating a new level tree for levels that refer to other levels.
    """
    new_level = fn(level)
    if new_level is not None: return new_level

    new_level_source = level.source if replace_source is None else replace_source
    if isinstance(level, LevelZero): return level # does not refer to any other level
    elif isinstance(level, LevelParam): return level # does not refer to any other level
    elif isinstance(level, LevelSucc): return LevelSucc(replace_level(level.anc, fn, replace_source=replace_source), source=new_level_source)
    elif isinstance(level, LevelMax): return LevelMax(replace_level(level.lhs, fn, replace_source=replace_source), replace_level(level.rhs, fn, replace_source=replace_source), source=new_level_source)
    elif isinstance(level, LevelIMax): return LevelIMax(replace_level(level.lhs, fn, replace_source=replace_source), replace_level(level.rhs, fn, replace_source=replace_source), source=new_level_source)
    else: raise PanicLevelError(f"Unknown level type {level.__class__.__name__}")

LevelSubList = List[Tuple[LevelParam, Level]]

def substitute_level_params_level(level : Level, params : LevelSubList, replace_source : Optional[Any]) -> Level:
    """ Replaces all level parameters in the given level with the given values. """
    def replace_fn(l : Level) -> Optional[Level]:
        for to_sub, value in params:
            if isinstance(l, LevelParam) and l.pname == to_sub.pname:
                return value
        return None
    return replace_level(level, replace_fn, replace_source=replace_source)

__all__ = ["are_unique_level_params", "is_equivalent", "is_equivalent_list", "make_imax"]

def do_fn_level_aux(level : Level, visited : Set[int], fn : Callable[[Level], None]) -> None:

    key = id(level)
    if key in visited: return
    visited.add(key)
    
    fn(level)

    if isinstance(level, LevelSucc): 
        do_fn_level_aux(level.anc, visited, fn)
    elif isinstance(level, LevelMax): 
        do_fn_level_aux(level.lhs, visited, fn)
        do_fn_level_aux(level.rhs, visited, fn)
    elif isinstance(level, LevelIMax): 
        do_fn_level_aux(level.lhs, visited, fn)
        do_fn_level_aux(level.rhs, visited, fn)

def do_fn_level(level : Level, fn : Callable[[Level], None]) :
    do_fn_level_aux(level, set(), fn)

def mark_as_external_level(level : Level):
    def mark_fn_level(e : Level):
        e.is_external = True
    do_fn_level(level, mark_fn_level)
    
def mark_as_expected_type_level(level : Level):
    def mark_fn_level(e : Level):
        e.is_expected_type = True
    do_fn_level(level, mark_fn_level)

def rename_level_params_with_index_level(level : Level, rename_dict : Dict[Name, int], replace_source : Optional[Any]) -> Level:
    def rename_fn_level(e : Level):
        if isinstance(e, LevelParam):
            if e.pname not in rename_dict:
                rename_dict[e.pname] = len(rename_dict)
            index = rename_dict[e.pname]
            return LevelParam(string_to_name(f"param_{index}"), source=e.source)
        return None
    return replace_level(level, rename_fn_level, replace_source=replace_source)