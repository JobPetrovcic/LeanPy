from enum import Enum
from typing import Callable, Dict, List, Optional, Sequence, Tuple, TypeVar

#from typeguard import typechecked

from LeanPy.Structures.Expression.Expression import *
from LeanPy.Structures.Expression.Level import Level, LevelParam
from LeanPy.Structures.Expression.LevelManipulation import substitute_level_params_level, LevelSubList

# for fvars we are relying on total equality
##@profile
#@typechecked

T = TypeVar('T')
def save_result(expr : T, new_expr : Expression, replace_cache : Dict[T, Expression]):
    replace_cache[expr] = new_expr

def replace_expression_aux(
        expr : Expression, 
        fn : Callable[[Expression], Optional[Expression]],
        replace_cache : Dict[Expression, Expression],
    ) -> Expression:
    
    # first check if we have already replaced this expression
    if expr in replace_cache: return replace_cache[expr]

    new_expr = fn(expr)
    if new_expr is None:
        if isinstance(expr, BVar): new_expr = expr
        elif isinstance(expr, FVar): new_expr = expr
        elif isinstance(expr, Sort): new_expr = expr
        elif isinstance(expr, Const): new_expr = expr
        elif isinstance(expr, App):
            r_fn = replace_expression_aux(expr.fn, fn, replace_cache)
            r_arg = replace_expression_aux(expr.arg, fn, replace_cache) 
            if expr.fn is r_fn and expr.arg is r_arg: new_expr = expr
            new_expr = App(fn=r_fn, arg=r_arg)
        elif isinstance(expr, Lambda): 
            r_arg_type = replace_expression_aux(expr.arg_type, fn, replace_cache)
            r_body = replace_expression_aux(expr.body, fn, replace_cache)
            if expr.arg_type is r_arg_type and expr.body is r_body: new_expr = expr
            new_expr = Lambda(bname=expr.bname, arg_type=r_arg_type, body=r_body)
        elif isinstance(expr, Pi): 
            r_arg_type = replace_expression_aux(expr.arg_type, fn, replace_cache)
            r_body_type = replace_expression_aux(expr.body_type, fn, replace_cache)
            if expr.arg_type is r_arg_type and expr.body_type is r_body_type: new_expr = expr
            new_expr = Pi(bname=expr.bname, arg_type=r_arg_type, body_type=r_body_type)
        elif isinstance(expr, Let): 
            r_arg_type = replace_expression_aux(expr.arg_type, fn, replace_cache)
            r_val = replace_expression_aux(expr.val, fn, replace_cache)
            r_body = replace_expression_aux(expr.body, fn, replace_cache)
            if expr.arg_type is r_arg_type and expr.val is r_val and expr.body is r_body: new_expr = expr
            new_expr = Let(bname=expr.bname, arg_type=r_arg_type, val=r_val, body=r_body)
        elif isinstance(expr, Proj): 
            r_expr = replace_expression_aux(expr.expr, fn, replace_cache)
            if expr.expr is r_expr: new_expr = expr
            new_expr = Proj(sname=expr.sname, index=expr.index, expr=r_expr)
        elif isinstance(expr, NatLit): new_expr = expr
        elif isinstance(expr, StrLit): new_expr = expr
        else: raise ValueError(f"Unknown expression type {expr.__class__.__name__}")
    
    save_result(expr, new_expr, replace_cache)

    return new_expr
    
def replace_expression(expr : Expression, fn : Callable[[Expression], Optional[Expression]]) -> Expression:
    """ 
    Recursively replaces subexpressions in the given expression using the given function. It does create a new expression tree. 

    Args:
        expr: The expression to replace subexpressions in.
        fn: The function to use to replace subexpressions. It should return None if the expression should not be replaced.
    
    NOTE: uses a cache to avoid recomputing the same expression multiple times. Thus the function fn should be pure.

    Returns:
        The new expression with subexpressions replaced.
    """
    return replace_expression_aux(expr, fn, {})

def replace_expression_w_depth_aux(
        expr : Expression, 
        fn : Callable[[Expression, int], Optional[Expression]],
        depth : int,
        replace_cache : Dict[Tuple[Expression, int], Expression]
    ) -> Expression:

    # first check if we have already replaced this expression
    key = (expr, depth)
    if key in replace_cache: return replace_cache[key]

    new_expr = fn(expr, depth)
    if new_expr is None:
        if isinstance(expr, BVar): new_expr = BVar(db_index=expr.db_index)
        elif isinstance(expr, FVar): new_expr = expr # fvars differentiate by reference
        elif isinstance(expr, Sort): new_expr = Sort(level=expr.level) # don't copy the level
        elif isinstance(expr, Const): new_expr = Const(cname=expr.cname, lvl_params=expr.lvl_params)  # don't copy the name
        elif isinstance(expr, App): 
            r_fn = replace_expression_w_depth_aux(expr.fn, fn, depth, replace_cache)
            r_arg = replace_expression_w_depth_aux(expr.arg, fn, depth, replace_cache)

            # if the function and argument are the same, new_expr = the original expression
            if expr.fn is r_fn and expr.arg is r_arg: new_expr = expr
            new_expr = App(
                fn=r_fn,
                arg=r_arg
            )
        elif isinstance(expr, Lambda):
            r_arg_type = replace_expression_w_depth_aux(expr.arg_type, fn, depth, replace_cache)
            r_body = replace_expression_w_depth_aux(expr.body, fn, depth + 1, replace_cache)
            if expr.arg_type is r_arg_type and expr.body is r_body: new_expr = expr
            new_expr = Lambda(
                bname=expr.bname, 
                arg_type=r_arg_type,
                body=r_body
            )
        elif isinstance(expr, Pi):
            r_arg_type = replace_expression_w_depth_aux(expr.arg_type, fn, depth, replace_cache)
            r_body_type = replace_expression_w_depth_aux(expr.body_type, fn, depth + 1, replace_cache)
            if expr.arg_type is r_arg_type and expr.body_type is r_body_type: new_expr = expr 
            new_expr = Pi(
                bname=expr.bname, 
                arg_type=r_arg_type,
                body_type=r_body_type
            )
        elif isinstance(expr, Let): 
            r_arg_type = replace_expression_w_depth_aux(expr.arg_type, fn, depth, replace_cache)
            r_val = replace_expression_w_depth_aux(expr.val, fn, depth, replace_cache)
            r_body = replace_expression_w_depth_aux(expr.body, fn, depth + 1, replace_cache)
            if expr.arg_type is r_arg_type and expr.val is r_val and expr.body is r_body: new_expr = expr
            new_expr = Let(
                bname=expr.bname, 
                arg_type=r_arg_type,
                val=r_val,
                body=r_body
            )
        elif isinstance(expr, Proj): 
            r_expr = replace_expression_w_depth_aux(expr.expr, fn, depth, replace_cache)
            if expr.expr is r_expr: new_expr = expr
            new_expr = Proj(
                sname=expr.sname, 
                index=expr.index, 
                expr=r_expr)
        elif isinstance(expr, NatLit): 
            new_expr = expr
        elif isinstance(expr, StrLit): 
            new_expr = expr
        else: raise ValueError(f"Unknown expression type {expr.__class__.__name__}")

    save_result((expr, depth), new_expr, replace_cache)
    return new_expr

##@profile
#@typechecked
def replace_expression_w_depth(expr : Expression, fn : Callable[[Expression, int], Optional[Expression]], depth :int) -> Expression:
    """ 
    Recursively replaces subexpressions in the given expression using the given function. It does by creating a new expression tree. 

    Args:
        expr: The expression to replace subexpressions in.
        fn: The function to use to replace subexpressions. It should return None if the expression should not be replaced.
    
    NOTE: uses a cache to avoid recomputing the same expression multiple times. Thus the function fn should be pure.
        
    Returns:
        The new expression with subexpressions replaced.
    """
    return replace_expression_w_depth_aux(expr, fn, depth, {})

##@profile
#@typechecked
def substitute_level_params_in_expression(body : Expression, params : LevelSubList) -> Expression:
    """ Replaces all level parameters in the given"""
    ##@profile
    def replace_level_params(expr : Expression) -> Optional[Expression]:
        if isinstance(expr, Sort):
            return Sort(level=substitute_level_params_level(expr.level, params)) # copy the levels since we are changing them
        elif isinstance(expr, Const):
            return Const(cname=expr.cname, lvl_params=[substitute_level_params_level(l, params) for l in expr.lvl_params]) # copy the levels since we are changing them
        return None

    return replace_expression(body, replace_level_params)

##@profile
#@typechecked
def instantiate_bvar(body : Expression, val : Expression) -> Expression:
    """
    Replaces the outermost bound variable in the given expression with the given free variable. Throws an error if it finds an unbound bvar index.
    """
    ##@profile
    def instantiation_fn(expr : Expression, depth : int) -> Optional[Expression]:
        if not has_loose_bvars(expr): return expr
        if isinstance(expr, BVar): 
            if expr.db_index == depth: return val
        return None
    return replace_expression_w_depth(body, instantiation_fn, 0)

def instantiate_bvars(body : Expression, vals : Sequence[Expression]) -> Expression:
    """
    Replaces the outermost bound variables in the given expression with the given free variables. Throws an error if it finds an unbound bvar index.
    """
    ##@profile
    def instantiation_fn(expr : Expression, depth : int) -> Optional[Expression]:
        if not has_loose_bvars(expr): return expr
        if isinstance(expr, BVar): 
            if expr.db_index >= depth: 
                if expr.db_index - depth < len(vals): return vals[expr.db_index - depth]
                else: raise ValueError(f"Unbound de Bruijn index {expr.db_index}")
        return None
    return replace_expression_w_depth(body, instantiation_fn, 0)

##@profile
#@typechecked
def abstract_bvar(body : Expression, fvar : FVar) -> Expression:
    # turns fvar into a bound variable with de Bruijn index depth
    ##@profile
    assert not has_loose_bvars(fvar.type), f"Cannot abstract a free variable with a loose bound variable in its type: {fvar}"
    if fvar.val is not None:
        assert not has_loose_bvars(fvar.val), f"Cannot abstract a free variable with a loose bound variable in its value: {fvar}"
    def abstraction_fn(expr : Expression, depth : int) -> Optional[Expression]:
        if not has_fvar(expr): return expr
        if isinstance(expr, FVar):
            if expr is fvar:
                return BVar(db_index=depth)
        return None
    
    return replace_expression_w_depth(body, abstraction_fn, 0)

def abstract_multiple_bvar(fvars : List[FVar], body : Expression) -> Expression:
    for fvar in fvars:
        assert not has_loose_bvars(fvar.type), f"Cannot abstract a free variable with a loose bound variable in its type: {fvar}"
        if fvar.val is not None:
            assert not has_loose_bvars(fvar.val), f"Cannot abstract a free variable with a loose bound variable in its value: {fvar}"
    """ Abstracts multiple free variables in the given expression. """
    ##@profile
    def replace_fn(expr : Expression, depth : int) -> Optional[Expression]:
        if not has_fvar(expr): return expr
        if isinstance(expr, FVar):
            for i, fvar in enumerate(fvars):
                if fvar is expr: return BVar(db_index=depth + i)
        return None
    return replace_expression_w_depth(body, replace_fn, 0)

def unfold_app(expr : Expression) -> Tuple[Expression, List[Expression]]:
    """ If expr is of form (... ((f a1) a2) ... an), returns f, [a1, a2, ..., an]. """
    fn, args = unfold_app_rev(expr)
    return fn, list(reversed(args))

##@profile
#@typechecked
def unfold_app_rev(expr : Expression) -> Tuple[Expression, List[Expression]]:
    """ If expr is of form (...((f a1) a2) ... an), returns f, [an, ..., a2, a1]. """
    fn = expr
    args : List[Expression] = []
    while isinstance(fn, App):
        args.append(fn.arg)
        fn = fn.fn
    return fn, args

def get_app_function(expr : Expression) -> Expression:
    """ If expr is of form (... ((f a1) a2) ... an), returns f. """
    while isinstance(expr, App):
        expr = expr.fn
    return expr

##@profile
#@typechecked
def fold_apps(fn : Expression, args : List[Expression]) -> Expression:
    """ Folds a function and a list of arguments into a single application expression. """
    result = fn
    for arg in args:
        result = App(fn=result, arg=arg)
    return result

def has_fvar(expr : Expression) -> bool:
    """ Returns True if the given expression contains a free variable. """
    return expr.num_fvars > 0

def level_zip(lvl_params : List[LevelParam], lvl_values : List[Level]) -> LevelSubList:
    """ Checks if the two lists of levels have the same length and zips them together. """
    if len(lvl_params) != len(lvl_values): raise ValueError("Found different number of level parameters.")
    return list(zip(lvl_params, lvl_values))

##@profile
#@typechecked
def get_binding_type(expr : Expression) -> Expression:
    """ Returns the type of the given binding expression. """
    if isinstance(expr, Lambda): return expr.arg_type
    elif isinstance(expr, Pi): return expr.arg_type

    raise ValueError(f"Can get binding type of Lambda or Pi, not {expr.__class__.__name__}")

##@profile
#@typechecked
def get_binding_body(expr : Expression) -> Expression:
    """ Returns the body of the given binding expression. """
    if isinstance(expr, Lambda): return expr.body
    elif isinstance(expr, Pi): return expr.body_type
    
    raise ValueError(f"Can get binding body of Lambda or Pi, not {expr.__class__.__name__}")

def has_loose_bvars(expr : Expression) -> bool:
    """ Returns True if the given expression has any loose bound variables. """
    return expr.bvar_range >= 0

class ReductionStatus(Enum):
    NOT_EQUAL = 0
    EQUAL = 1
    CONTINUE = 2
    UNKNOWN = 3