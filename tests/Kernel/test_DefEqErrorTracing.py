from LeanPy.Kernel.KernelErrors import DefinitionalEqualityError
from LeanPy.Structures.Expression.Level import *
from LeanPy.Structures.Expression.Expression import *
from LeanPy.Kernel.TypeChecker import TypeChecker
from LeanPy.Structures.Name import string_to_name

def test_defeq_tracing1():
    pi1 = Pi(string_to_name("x"), Sort(LevelZero(), source=None), Sort(LevelZero(), source=None), source=None)
    pi2 = Pi(string_to_name("x"), Sort(LevelSucc(LevelZero()), source=None), Sort(LevelZero(), source=None), source=None)
    tc = TypeChecker()
    try:
        tc.def_eq(pi1, pi2, True)
        assert False
    except DefinitionalEqualityError as e:
        assert e.l.source is pi1.domain
        assert e.r.source is pi2.domain

def test_defeq_tracing2():
    pi1 = Lambda(string_to_name("x"), Sort(LevelZero(), source=None), Sort(LevelZero(), source=None), source=None)
    pi2 = Lambda(string_to_name("x"), Sort(LevelSucc(LevelZero()), source=None), Sort(LevelZero(), source=None), source=None)
    tc = TypeChecker()
    try:
        tc.def_eq(pi1, pi2, True)
        assert False
    except DefinitionalEqualityError as e:
        assert e.l.source is pi1.domain
        assert e.r.source is pi2.domain

def test_defeq_tracing3():
    pi1 = Pi(string_to_name("x"), Sort(LevelZero(), source=None), Sort(LevelZero(), source=None), source=None)
    pi2 = Pi(string_to_name("x"), Sort(LevelZero(), source=None), Sort(LevelSucc(LevelZero()), source=None), source=None)
    tc = TypeChecker()
    try:
        tc.def_eq(pi1, pi2, True)
        assert False
    except DefinitionalEqualityError as e:
        assert e.l.source is pi1.codomain
        assert e.r.source is pi2.codomain

def test_defeq_tracing_and_infer():
    lam = Lambda(string_to_name("x"), Sort(LevelZero(), source=None), Sort(LevelZero(), source=None), source=None)
    pi = Pi(string_to_name("x"), Sort(LevelZero(), source=None), Sort(LevelZero(), source=None), source=None)

    tc = TypeChecker()

    inferred_lam_type = tc.infer(lam)
    assert inferred_lam_type.source is lam
    assert isinstance(inferred_lam_type, Pi)
    assert inferred_lam_type.domain.source is lam.domain
    assert inferred_lam_type.codomain.source is lam.body
    try:
        tc.def_eq(inferred_lam_type, pi, True)
        assert False
    except DefinitionalEqualityError as e:
        assert e.l.source is lam.body
        assert e.r.source is pi.codomain
