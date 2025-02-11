from LeanPy.Kernel.KernelErrors import KernelError
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
