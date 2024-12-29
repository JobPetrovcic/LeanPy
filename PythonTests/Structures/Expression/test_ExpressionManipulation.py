from typeguard import typechecked
from Structures.Expression.ExpressionManipulation import fold_apps, unfold_app
from Structures.Expression.Expression import App, Const
from Structures.Name import Anonymous, SubName

@typechecked
def create_name(name : str):
    return SubName(Anonymous(), name)

def test_fold_unfold_apps():
    # Create a nested application expression: ((f a) b) c 
    f = Const(name=create_name("f"), lvl_params=[])
    a = Const(name=create_name("a"), lvl_params=[])
    b = Const(name=create_name("b"), lvl_params=[])
    c = Const(name=create_name("c"), lvl_params=[])
    expr = App(App(App(f, a), b), c)
    
    # Test that unfold then fold returns same expression
    fn, args = unfold_app(expr)
    folded = fold_apps(fn, args)
    
    for x, y in zip(unfold_app(folded)[1], unfold_app(expr)[1]):
        assert isinstance(x, Const)
        assert isinstance(y, Const)
        assert x.name == y.name