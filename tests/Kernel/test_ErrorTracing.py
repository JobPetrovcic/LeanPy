from LeanPy.Kernel.KernelErrors import KernelError
from LeanPy.Structures.Expression.Level import *
from LeanPy.Structures.Expression.Expression import *
from LeanPy.Kernel.TypeChecker import TypeChecker

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