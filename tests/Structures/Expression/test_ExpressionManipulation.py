from typeguard import typechecked
from LeanPy.Structures.Expression.ExpressionManipulationDebug import fold_apps, unfold_app
from LeanPy.Structures.Expression.ExpressionDebug import App, Const, Pi, Sort
from LeanPy.Structures.Expression.Level import LevelZero
from LeanPy.Structures.Name import Anonymous, SubName

@typechecked
def create_name(name : str):
    return SubName(Anonymous(), name)

def test_fold_unfold_apps():
    # Create a nested application expression: ((f a) b) c 
    f = Const(cname=create_name("f"), lvl_params=[])
    a = Const(cname=create_name("a"), lvl_params=[])
    b = Const(cname=create_name("b"), lvl_params=[])
    c = Const(cname=create_name("c"), lvl_params=[])
    expr = App(App(App(f, a), b), c)
    
    # Test that unfold then fold returns same expression
    fn, args = unfold_app(expr)
    folded = fold_apps(fn, args)
    
    for x, y in zip(unfold_app(folded)[1], unfold_app(expr)[1]):
        assert isinstance(x, Const)
        assert isinstance(y, Const)
        assert x.cname == y.cname

def test_bvar_range():
    f = Sort(LevelZero())
    assert f.bvar_range == -1
    y = Sort(LevelZero())
    assert f.bvar_range == -1

    pi = Pi(create_name("x"), f, y)
    assert pi.bvar_range == -1