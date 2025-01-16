from enum import Enum
from typing import Callable, List, Optional, Sequence, Tuple

from typeguard import typechecked

from Structures.Expression.Expression import *
from Structures.Expression.Level import Level, LevelParam
from Structures.Expression.LevelManipulation import substitute_level_params_level, LevelSubList

# for fvars we are relying on total equality
@typechecked
def replace_expression(expr : Expression, fn : Callable[[Expression], Optional[Expression]]) -> Expression:
    """ 
    Recursively replaces subexpressions in the given expression using the given function. It does by creating a new expression tree. 

    Args:
        expr: The expression to replace subexpressions in.
        fn: The function to use to replace subexpressions. It should return None if the expression should not be replaced.
    
    Returns:
        The new expression with subexpressions replaced.
    """
    new_expr = fn(expr)
    if new_expr is not None: return new_expr

    if isinstance(expr, BVar): return expr
    elif isinstance(expr, FVar): return expr
    elif isinstance(expr, Sort): return expr
    elif isinstance(expr, Const): return expr
    elif isinstance(expr, App): return App(fn=replace_expression(expr.fn, fn), arg=replace_expression(expr.arg, fn))
    elif isinstance(expr, Lambda): return Lambda(bname=expr.bname, arg_type=replace_expression(expr.arg_type, fn), body=replace_expression(expr.body, fn))
    elif isinstance(expr, Pi): return Pi(bname=expr.bname, arg_type=replace_expression(expr.arg_type, fn), body_type=replace_expression(expr.body_type, fn))
    elif isinstance(expr, Let): return Let(bname=expr.bname, arg_type=replace_expression(expr.arg_type, fn), val=replace_expression(expr.val, fn), body=replace_expression(expr.body, fn))
    elif isinstance(expr, Proj): return Proj(type_name=expr.type_name, index=expr.index, struct=replace_expression(expr.struct, fn))
    elif isinstance(expr, NatLit): return expr
    elif isinstance(expr, StringLit): return expr
    else: raise ValueError(f"Unknown expression type {expr.__class__.__name__}")

@typechecked
def replace_expression_w_depth(expr : Expression, fn : Callable[[Expression, int], Optional[Expression]], depth :int) -> Expression:
    """ 
    Recursively replaces subexpressions in the given expression using the given function. It does by creating a new expression tree. 

    Args:
        expr: The expression to replace subexpressions in.
        fn: The function to use to replace subexpressions. It should return None if the expression should not be replaced.
    
    Returns:
        The new expression with subexpressions replaced.
    """
    new_expr = fn(expr, depth)
    if new_expr is not None: return new_expr

    if isinstance(expr, BVar): return BVar(dbj_id=expr.dbj_id)
    elif isinstance(expr, FVar): return expr # fvars differentiate by reference
    elif isinstance(expr, Sort): return Sort(level=expr.level) # don't copy the level
    elif isinstance(expr, Const): return Const(name=expr.name, lvl_params=expr.lvl_params)  # don't copy the name
    elif isinstance(expr, App): 
        return App(
            fn=replace_expression_w_depth(expr.fn, fn, depth), 
            arg=replace_expression_w_depth(expr.arg, fn, depth)
        )
    elif isinstance(expr, Lambda): 
        return Lambda(
            bname=expr.bname, 
            arg_type=replace_expression_w_depth(expr.arg_type, fn, depth), 
            body=replace_expression_w_depth(expr.body, fn, depth + 1))
    elif isinstance(expr, Pi): 
        return Pi(
            bname=expr.bname, 
            arg_type=replace_expression_w_depth(expr.arg_type, fn, depth), 
            body_type=replace_expression_w_depth(expr.body_type, fn, depth + 1)
        )
    elif isinstance(expr, Let): 
        return Let(
            bname=expr.bname, 
            arg_type=replace_expression_w_depth(expr.arg_type, fn, depth), 
            val=replace_expression_w_depth(expr.val, fn, depth), 
            body=replace_expression_w_depth(expr.body, fn, depth + 1))
    elif isinstance(expr, Proj): 
        return Proj(
            type_name=expr.type_name, 
            index=expr.index, 
            struct=replace_expression_w_depth(expr.struct, fn, depth))
    elif isinstance(expr, NatLit): 
        return expr
    elif isinstance(expr, StringLit): 
        return expr
    else: raise ValueError(f"Unknown expression type {expr.__class__.__name__}")

@typechecked
def do_fn(expr : Expression, fn : Callable[[Expression], None]):
    """ Applies the given function to all subexpressions in the given expression. """
    fn(expr)
    if isinstance(expr, BVar) or isinstance(expr, FVar) or isinstance(expr, Sort) or isinstance(expr, Const): pass
    elif isinstance(expr, App):
        do_fn(expr.fn, fn)
        do_fn(expr.arg, fn)
    elif isinstance(expr, Lambda):
        do_fn(expr.arg_type, fn)
        do_fn(expr.body, fn)
    elif isinstance(expr, Pi):
        do_fn(expr.arg_type, fn)
        do_fn(expr.body_type, fn)
    elif isinstance(expr, Let):
        do_fn(expr.arg_type, fn)
        do_fn(expr.val, fn)
        do_fn(expr.body, fn)
    elif isinstance(expr, Proj):
        do_fn(expr.struct, fn)
    elif isinstance(expr, NatLit) or isinstance(expr, StringLit): pass
    else: raise ValueError(f"Unknown expression type {expr.__class__.__name__}")

def do_fn_w_depth(expr : Expression, fn : Callable[[Expression, int], None], depth : int):
    fn(expr, depth)
    if isinstance(expr, BVar) or isinstance(expr, FVar) or isinstance(expr, Sort) or isinstance(expr, Const): pass
    elif isinstance(expr, App):
        do_fn_w_depth(expr.fn, fn, depth)
        do_fn_w_depth(expr.arg, fn, depth)
    elif isinstance(expr, Lambda):
        do_fn_w_depth(expr.arg_type, fn, depth)
        do_fn_w_depth(expr.body, fn, depth + 1)
    elif isinstance(expr, Pi):
        do_fn_w_depth(expr.arg_type, fn, depth)
        do_fn_w_depth(expr.body_type, fn, depth + 1)
    elif isinstance(expr, Let):
        do_fn_w_depth(expr.arg_type, fn, depth)
        do_fn_w_depth(expr.val, fn, depth)
        do_fn_w_depth(expr.body, fn, depth + 1)
    elif isinstance(expr, Proj):
        do_fn_w_depth(expr.struct, fn, depth)
    elif isinstance(expr, NatLit) or isinstance(expr, StringLit): pass
    else: raise ValueError(f"Unknown expression type {expr.__class__.__name__}")

@typechecked
def substitute_level_params_in_expression(body : Expression, params : LevelSubList) -> Expression:
    """ Replaces all level parameters in the given"""
    def replace_level_params(expr : Expression) -> Optional[Expression]:
        if isinstance(expr, Sort):
            return Sort(level=substitute_level_params_level(expr.level, params)) # copy the levels since we are changing them
        elif isinstance(expr, Const):
            return Const(name=expr.name, lvl_params=[substitute_level_params_level(l, params) for l in expr.lvl_params]) # copy the levels since we are changing them
        return None

    return replace_expression(body, replace_level_params)

@typechecked
def instantiate_bvar(body : Expression, val : Expression) -> Expression:
    """
    Replaces the outermost bound variable in the given expression with the given free variable. Throws an error if it finds an unbound bvar index.
    """
    def intantiation_fn(expr : Expression, depth : int) -> Optional[Expression]:
        if isinstance(expr, BVar): 
            if expr.dbj_id == depth: return val
        return None
    return replace_expression_w_depth(body, intantiation_fn, 0)

def instantiate_bvars(body : Expression, vals : Sequence[Expression]) -> Expression:
    """
    Replaces the outermost bound variables in the given expression with the given free variables. Throws an error if it finds an unbound bvar index.
    """
    def instantiation_fn(expr : Expression, depth : int) -> Optional[Expression]:
        if isinstance(expr, BVar): 
            if expr.dbj_id >= depth: 
                if expr.dbj_id - depth < len(vals): return vals[expr.dbj_id - depth]
                else: raise ValueError(f"Unbound de Bruijn index {expr.dbj_id}")
        return None
    return replace_expression_w_depth(body, instantiation_fn, 0)

@typechecked
def abstract_bvar(body : Expression, fvar : FVar) -> Expression:
    # turns fvar into a bound variable with de Bruijn index depth
    def abstraction_fn(expr : Expression, depth : int) -> Optional[Expression]:
        if isinstance(expr, FVar):
            if expr is fvar:
                return BVar(dbj_id=depth)
        return None
    
    return replace_expression_w_depth(body, abstraction_fn, 0)

def abstract_multiple_bvar(fvars : List[FVar], body : Expression) -> Expression:
    """ Abstracts multiple free variables in the given expression. """
    def replace_fn(expr : Expression, depth : int) -> Optional[Expression]:
        if isinstance(expr, FVar):
            for i, fvar in enumerate(fvars):
                if fvar is expr: return BVar(dbj_id=depth + i)
        return None
    return replace_expression_w_depth(body, replace_fn, 0)

def unfold_app(expr : Expression) -> Tuple[Expression, List[Expression]]:
    """ If expr is of form (... ((f a1) a2) ... an), returns f, [a1, a2, ..., an]. """
    fn, args = unfold_app_rev(expr)
    return fn, list(reversed(args))

@typechecked
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

@typechecked
def fold_apps(fn : Expression, args : List[Expression]) -> Expression:
    """ Folds a function and a list of arguments into a single application expression. """
    result = fn
    for arg in args:
        result = App(fn=result, arg=arg)
    return result

#@typechecked
#def clone_expression(expr : Expression) -> Expression:
#    """ Clones the given expression. """
#    def clone_fn(expr : Expression) -> Optional[Expression]:
#        return None
#    return replace_expression(expr, clone_fn)

@typechecked
def has_specific_fvar(expr : Expression, fvar : FVar) -> bool:
    """ Returns True if the given expression contains the given free variable. """
    has_fvar = False
    def fn(expr : Expression):
        nonlocal has_fvar
        if isinstance(expr, FVar) and (expr is fvar): has_fvar = True
    do_fn(expr, fn)
    return has_fvar

def has_fvar(expr : Expression) -> bool:
    """ Returns True if the given expression contains a free variable. """
    has_fvar = False
    def fn(expr : Expression):
        nonlocal has_fvar
        if isinstance(expr, FVar): has_fvar = True
    do_fn(expr, fn)
    return has_fvar

def level_zip(lvl_params : List[LevelParam], lvl_values : List[Level]) -> LevelSubList:
    """ Checks if the two lists of levels have the same length and zips them together. """
    if len(lvl_params) != len(lvl_values): raise ValueError("Found different number of level parameters.")
    return list(zip(lvl_params, lvl_values))

@typechecked
def get_binding_type(expr : Expression) -> Expression:
    """ Returns the type of the given binding expression. """
    if isinstance(expr, Lambda): return expr.arg_type
    elif isinstance(expr, Pi): return expr.arg_type

    raise ValueError(f"Can get binding type of Lambda or Pi, not {expr.__class__.__name__}")

@typechecked
def get_binding_body(expr : Expression) -> Expression:
    """ Returns the body of the given binding expression. """
    if isinstance(expr, Lambda): return expr.body
    elif isinstance(expr, Pi): return expr.body_type
    
    raise ValueError(f"Can get binding body of Lambda or Pi, not {expr.__class__.__name__}")

def has_loose_bvars(expr : Expression) -> bool:
    """ Returns True if the given expression has any loose bound variables. """
    has_loose = False
    def is_loose_bvarfn(expr : Expression, depth : int):
        nonlocal has_loose
        if isinstance(expr, BVar) and expr.dbj_id == depth: has_loose = True
        
    do_fn_w_depth(expr, is_loose_bvarfn, 0)

    return has_loose

class ReductionStatus(Enum):
    NOT_EQUAL = 0
    EQUAL = 1
    CONTINUE = 2
    UNKNOWN = 3