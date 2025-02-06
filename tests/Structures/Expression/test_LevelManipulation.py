from LeanPy.Structures.Expression.Level import *
from LeanPy.Structures.Expression.LevelManipulation import from_offset, is_equivalent, lt_compare, make_imax, normalize, key_lt
from LeanPy.Structures.Name import *

def test_normalize1():
    t = LevelIMax(LevelSucc(LevelZero()), LevelSucc(LevelZero()))
    nt = normalize(t)
    assert nt.totally_equal(LevelSucc(LevelZero())),  f"Expected {LevelSucc(LevelZero())} but got {nt}"

def test_normalize2():
    # IMax(Max(1, 1), 1) -> 1
    t = LevelIMax(LevelMax(LevelSucc(LevelZero()), LevelSucc(LevelZero())), LevelSucc(LevelZero()))
    nt = normalize(t)
    assert nt.totally_equal(LevelSucc(LevelZero())), f"Expected {LevelSucc(LevelZero())} but got {nt}"

def test_normalize3():
    # Max(1, 1) -> 1
    t = LevelMax(LevelSucc(LevelZero()),LevelSucc(LevelZero()))
    nt = normalize(t)
    assert nt.totally_equal(LevelSucc(LevelZero())), f"Expected {LevelSucc(LevelZero())} but got {nt}"

def create_name(name : str):
    return SubName(Anonymous(), name)

def test_normalize4():
    # IMax(Max(1, 1 + u), 1 + u) -> 1 + u
    u = create_name("u")
    t = LevelIMax(LevelMax(LevelSucc(LevelZero()), LevelSucc(LevelParam(u))), LevelSucc(LevelParam(u)))
    nt = normalize(t)
    assert nt.totally_equal(LevelSucc(LevelParam(u))), f"Expected {LevelSucc(LevelParam(u))} but got {nt}"

def test_lt_compare():
    # 0 < 1 + u
    t = lt_compare(LevelZero(), LevelSucc(LevelParam(create_name("u"))))
    assert t == -1, f"Expected -1 but got {t}"

    lst = [LevelSucc(LevelParam(create_name("u"))), LevelSucc(LevelZero()), LevelZero()]
    lst.sort(key = key_lt)
    assert lst[0].totally_equal(LevelZero()), f"Expected {LevelZero()} but got {lst[0]}"

def test_imax_norm():
    # IMax(1 + u, 0) -> 0
    u = create_name("u")
    t = make_imax(LevelSucc(LevelParam(u)), LevelZero())
    nt = normalize(t)
    assert nt.totally_equal(LevelZero()), f"Expected {LevelZero()} but got {nt}"

def test_max_norm():
    # IMax(1 + u, 1) -> 1 + u
    u = create_name("u")
    t = LevelIMax(LevelSucc(LevelParam(u)), LevelSucc(LevelZero()))
    nt = normalize(t)
    assert nt.totally_equal(LevelSucc(LevelParam(u))), f"Expected {LevelSucc(LevelParam(u))} but got {nt}"

def test_from_offset():
    u = create_name("u")
    t = LevelParam(u)
    nt = from_offset(t, 1)
    assert nt.totally_equal(LevelSucc(LevelParam(u))), f"Expected {LevelSucc(LevelParam(u))} but got {nt}"

def test_normalize5():
    #  1 + Max(u_2, u_1) = Max 1+u_2 1+u_1
    u_1 = create_name("u_1")
    v_1 = create_name("v_1")

    t1 = LevelSucc(LevelMax(LevelParam(u_1), LevelParam(v_1)))
    nt1 = normalize(t1)
    t2 = LevelMax(LevelSucc(LevelParam(u_1)), LevelSucc(LevelParam(v_1)))
    nt2 = normalize(t2)
    assert nt1.totally_equal(nt2), f"Expected {nt2} but got {nt1}"

def test_normalize6():
    # IMax(1 + u, IMax(1 + u, IMax(u, IMax(u, IMax(0, IMax(0, 0)))))) = 0
    u = create_name("u")
    t = LevelIMax(LevelSucc(LevelParam(u)), LevelIMax(LevelSucc(LevelParam(u)), LevelIMax(LevelParam(u), LevelIMax(LevelParam(u), LevelIMax(LevelZero(), LevelIMax(LevelZero(), LevelZero()))))))
    print(t)
    nt = normalize(t)
    assert isinstance(nt, LevelZero), f"Expected {LevelZero()} but got {nt}"

    assert is_equivalent(t, LevelZero()), f"Expected {nt} but got {t}"

def test_normalize7():
    # imax (u_2 + 1) (u_1 + 1) + 1 = max (u_2 + 2) (u_1 + 2)
    u_1 = create_name("u_1")
    u_2 = create_name("u_2")
    t1 = LevelSucc(LevelIMax(LevelSucc(LevelParam(u_2)), LevelSucc(LevelParam(u_1))))
    
    nt1 = normalize(t1)

    t2 = LevelMax(LevelSucc(LevelSucc(LevelParam(u_2))), LevelSucc(LevelSucc(LevelParam(u_1))))
    nt2 = normalize(t2)

    print(nt1)
    print(nt2)

    assert nt1.totally_equal(nt2), f"Expected {nt2} but got {nt1}"

def test_noramlize8():
    # max (u_1 + 1) (u_2 + 1) + 1 = max (u_1 + 2) (u_2 + 2)
    u_1 = create_name("u_1")
    u_2 = create_name("u_2")
    t1 = LevelSucc(LevelMax(LevelSucc(LevelParam(u_1)), LevelSucc(LevelParam(u_2))))
    t2 = LevelMax(LevelSucc(LevelSucc(LevelParam(u_1))), LevelSucc(LevelSucc(LevelParam(u_2))))
    nt1 = normalize(t1)
    nt2 = normalize(t2)
    assert nt1.totally_equal(nt2), f"Expected {nt2} but got {nt1}"