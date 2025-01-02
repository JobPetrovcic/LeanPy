from Structures.Expression.Level import *
from Structures.Expression.LevelManipulation import equally_defined, lt_compare, make_imax, normalize, key_lt
from Structures.Name import *

def test_normalize1():
    t = LevelIMax(LevelSucc(LevelZero()), LevelSucc(LevelZero()))
    nt = normalize(t)
    assert equally_defined(nt, LevelSucc(LevelZero())), f"Expected {LevelSucc(LevelZero())} but got {nt}"

def test_normalize2():
    # IMax(Max(1, 1), 1) -> 1
    t = LevelIMax(LevelMax(LevelSucc(LevelZero()), LevelSucc(LevelZero())), LevelSucc(LevelZero()))
    nt = normalize(t)
    assert equally_defined(nt, LevelSucc(LevelZero())), f"Expected {LevelSucc(LevelZero())} but got {nt}"

def test_normalize3():
    # Max(1, 1) -> 1
    t = LevelMax(LevelSucc(LevelZero()), LevelSucc(LevelZero()))
    nt = normalize(t)
    assert equally_defined(nt, LevelSucc(LevelZero())), f"Expected {LevelSucc(LevelZero())} but got {nt}"

def create_name(name : str):
    return SubName(Anonymous(), name)

def test_normalize4():
    # IMax(Max(1, 1 + u), 1 + u) -> 1 + u
    u = create_name("u")
    t = LevelIMax(LevelMax(LevelSucc(LevelZero()), LevelSucc(LevelParam(u))), LevelSucc(LevelParam(u)))
    nt = normalize(t)
    assert equally_defined(nt, LevelSucc(LevelParam(u))), f"Expected {LevelSucc(LevelParam(u))} but got {nt}"

def test_lt_compare():
    # 0 < 1 + u
    t = lt_compare(LevelZero(), LevelSucc(LevelParam(create_name("u"))))
    assert t == -1, f"Expected -1 but got {t}"

    lst = [LevelSucc(LevelParam(create_name("u"))), LevelSucc(LevelZero()), LevelZero()]
    lst.sort(key = key_lt)
    assert equally_defined(lst[0], LevelZero()), f"Expected {LevelZero()} but got {lst[0]}"

def test_imax_norm():
    # IMax(1 + u, 0) -> 0
    u = create_name("u")
    t = make_imax(LevelSucc(LevelParam(u)), LevelZero())
    nt = normalize(t)
    assert equally_defined(nt, LevelZero()), f"Expected {LevelZero()} but got {nt}"

def test_max_norm():
    # IMax(1 + u, 1) -> 1 + u
    u = create_name("u")
    t = LevelIMax(LevelSucc(LevelParam(u)), LevelSucc(LevelZero()))
    nt = normalize(t)
    assert equally_defined(nt, LevelSucc(LevelParam(u))), f"Expected {LevelSucc(LevelParam(u))} but got {nt}"