from LeanPy.Kernel.KernelErrors import KernelError, UnfinishedExpressionError
from LeanPy.Parsing.DependencyManager import DependencyManager
from LeanPy.Structures.Expression.Level import *
from LeanPy.Structures.Expression.Expression import *
from LeanPy.Kernel.TypeChecker import TypeChecker
from LeanPy.Structures.Name import string_to_name

def test_tracing1():
    tc = TypeChecker()

    fn = Sort(LevelZero(), source=None)
    arg = Sort(LevelZero(), source=None)

    app = App(fn, arg, source=None)

    # tc.infer(app) must raise an error
    try:
        tc.infer(app)
        assert False
    except KernelError as e:
        assert e.source is app

def test_tracing2():
    tc = TypeChecker()

    proj_expr = Sort(LevelZero(), source=None)
    proj = Proj(string_to_name("Dummy"), 0, proj_expr, source=None) # Invalid projection

    try:
        tc.infer(proj)
        assert False
    except KernelError as e:
        assert e.source is proj

def test_tracing3():
    tc = TypeChecker()

    fn = Lambda(string_to_name("x"), Sort(LevelZero(), source=None), BVar(0, source=None), source=None)

    inferred_type = tc.infer(fn)

    assert inferred_type.source is fn
    assert isinstance(inferred_type, Pi)
    assert inferred_type.domain.source is fn.domain
    assert inferred_type.codomain.source is fn

#def test_mvar_infer():
#    tc = TypeChecker()
#
#    unfinished_pi = Pi(string_to_name("x"), Sort(LevelZero()), MVar())
#
#    inferred_type = tc.infer(unfinished_pi)

    #assert isinstance(inferred_type, Sort)
    #assert inferred_type.domain == Sort(LevelZero())
    #assert inferred_type.codomain == MVar()

some_constants = [
    "Eq",
    "OfNat.ofNat",
    "Nat",
    "Nat.zero",
    "Nat.succ",
]

def test_app_mvar():
    dir = "/home/jp/projects/Mathlib4Extraction/mathlib4/json_dump"
    dm = DependencyManager(dir, preloaded_declarations=some_constants)

    # @Eq.{1} @Nat @Nat.zero MVar
    expr = App(App(App(Const(string_to_name("Eq"), [LevelSucc(LevelZero())]), Const(string_to_name("Nat"), [])), Const(string_to_name("Nat.zero"), [])), MVar())

    try:
        dm.type_checker.infer(expr)
        assert False
    except UnfinishedExpressionError as e:
        pass