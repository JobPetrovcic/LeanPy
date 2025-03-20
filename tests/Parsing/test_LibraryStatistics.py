from LeanPy.Parsing.LibraryStatistics import statistics_expression_fn
from LeanPy.Structures.Expression.Expression import Sort, Const, Lambda
from LeanPy.Structures.Expression.Level import LevelZero
from LeanPy.Structures.Name import string_to_name

def test_statistics_sort():
    # Create a simple Sort expression with a LevelZero level.
    expr = Sort(LevelZero())
    constructor_count, root_depth, context_lens, leaf_count = statistics_expression_fn(expr)
    
    # Expect one Sort node and one level node (from LevelZero)
    assert constructor_count.get(Sort, 0) == 1
    assert constructor_count.get(LevelZero, 0) == 1
    # For a single node, depth_fn should return 1 and the traversal should visit one node (depth 0).
    assert root_depth == 1
    assert context_lens.get(0, 0) == 1
    # Sort is considered a leaf in this context.
    assert leaf_count == 1

def test_statistics_const():
    # Create a Const expression with no level parameters.
    expr = Const(string_to_name("c"), lvl_params=[])
    constructor_count, root_depth, context_lens, leaf_count = statistics_expression_fn(expr)
    
    # Expect one Const node; no level nodes are added because lvl_params is empty.
    assert constructor_count.get(Const, 0) == 1
    assert root_depth == 1
    assert context_lens.get(0, 0) == 1
    # Const is considered a leaf.
    assert leaf_count == 1

def test_statistics_lambda():
    c = Const(string_to_name("c"), lvl_params=[])
    expr = Lambda(string_to_name("x"), Sort(LevelZero()), c)
    constructor_count, root_depth, context_lens, leaf_count = statistics_expression_fn(expr)

    assert context_lens.get(0, 0) == 2
    assert context_lens.get(1, 0) == 1 # the body of the lambda