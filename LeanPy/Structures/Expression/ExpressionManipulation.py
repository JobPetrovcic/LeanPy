from enum import Enum
from typing import Callable, Dict, List, Optional, Sequence, Set, Tuple, TypeVar

from LeanPy.Structures.Expression.Expression import *
from LeanPy.Structures.Expression.Level import Level, LevelParam
from LeanPy.Structures.Expression.LevelManipulation import substitute_level_params_level, LevelSubList

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
            else: new_expr = App(fn=r_fn, arg=r_arg)
        elif isinstance(expr, Lambda): 
            r_domain = replace_expression_aux(expr.domain, fn, replace_cache)
            r_body = replace_expression_aux(expr.body, fn, replace_cache)
            if expr.domain is r_domain and expr.body is r_body: new_expr = expr
            else: new_expr = Lambda(bname=expr.bname, domain=r_domain, body=r_body)
        elif isinstance(expr, Pi): 
            r_domain = replace_expression_aux(expr.domain, fn, replace_cache)
            r_codomain = replace_expression_aux(expr.codomain, fn, replace_cache)
            if expr.domain is r_domain and expr.codomain is r_codomain: new_expr = expr
            else: new_expr = Pi(bname=expr.bname, domain=r_domain, codomain=r_codomain)
        elif isinstance(expr, Let): 
            r_domain = replace_expression_aux(expr.domain, fn, replace_cache)
            r_val = replace_expression_aux(expr.val, fn, replace_cache)
            r_body = replace_expression_aux(expr.body, fn, replace_cache)
            if expr.domain is r_domain and expr.val is r_val and expr.body is r_body: new_expr = expr
            else: new_expr = Let(bname=expr.bname, domain=r_domain, val=r_val, body=r_body)
        elif isinstance(expr, Proj): 
            r_expr = replace_expression_aux(expr.expr, fn, replace_cache)
            if expr.expr is r_expr: new_expr = expr
            else: new_expr = Proj(sname=expr.sname, index=expr.index, expr=r_expr)
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
            else: new_expr = App(
                fn=r_fn,
                arg=r_arg
            )
        elif isinstance(expr, Lambda):
            r_domain = replace_expression_w_depth_aux(expr.domain, fn, depth, replace_cache)
            r_body = replace_expression_w_depth_aux(expr.body, fn, depth + 1, replace_cache)
            if expr.domain is r_domain and expr.body is r_body: new_expr = expr
            else: new_expr = Lambda(
                bname=expr.bname, 
                domain=r_domain,
                body=r_body
            )
        elif isinstance(expr, Pi):
            r_domain = replace_expression_w_depth_aux(expr.domain, fn, depth, replace_cache)
            r_codomain = replace_expression_w_depth_aux(expr.codomain, fn, depth + 1, replace_cache)
            if expr.domain is r_domain and expr.codomain is r_codomain: new_expr = expr 
            else: new_expr = Pi(
                bname=expr.bname, 
                domain=r_domain,
                codomain=r_codomain
            )
        elif isinstance(expr, Let): 
            r_domain = replace_expression_w_depth_aux(expr.domain, fn, depth, replace_cache)
            r_val = replace_expression_w_depth_aux(expr.val, fn, depth, replace_cache)
            r_body = replace_expression_w_depth_aux(expr.body, fn, depth + 1, replace_cache)
            if expr.domain is r_domain and expr.val is r_val and expr.body is r_body: new_expr = expr
            else: new_expr = Let(
                bname=expr.bname, 
                domain=r_domain,
                val=r_val,
                body=r_body
            )
        elif isinstance(expr, Proj): 
            r_expr = replace_expression_w_depth_aux(expr.expr, fn, depth, replace_cache)
            if expr.expr is r_expr: new_expr = expr
            else: new_expr = Proj(
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

def do_fn_aux(e : Expression, visited : Set[Expression], fn : Callable[[Expression], None]):
    if e in visited: return
    fn(e)
    visited.add(e)
    
    if isinstance(e, App):
        do_fn_aux(e.fn, visited, fn)
        do_fn_aux(e.arg, visited, fn)
    elif isinstance(e, Lambda):
        do_fn_aux(e.domain, visited, fn)
        do_fn_aux(e.body, visited, fn)
    elif isinstance(e, Pi):
        do_fn_aux(e.domain, visited, fn)
        do_fn_aux(e.codomain, visited, fn)
    elif isinstance(e, Let):
        do_fn_aux(e.domain, visited, fn)
        do_fn_aux(e.val, visited, fn)
        do_fn_aux(e.body, visited, fn)
    elif isinstance(e, Proj):
        do_fn_aux(e.expr, visited, fn)

def do_fn(e : Expression, fn : Callable[[Expression], None]):
    do_fn_aux(e, set(), fn)

def mark_used(fvars : List[FVar], expr : Expression, used : List[bool]):
    """
    Marks the fvars that are used in the given expression. Used should be the same length as fvars and will be modified in place.
    """
    assert len(fvars) <= len(used)
    def mark_fn(e : Expression):
        if isinstance(e, FVar):
            for i, fvar in enumerate(fvars):
                if fvar is e: used[i] = True
    do_fn(expr, mark_fn)

def substitute_level_params_in_expression(body : Expression, params : LevelSubList) -> Expression:
    """ Replaces all level parameters in the given"""
    def replace_level_params(expr : Expression) -> Optional[Expression]:
        if isinstance(expr, Sort):
            return Sort(level=substitute_level_params_level(expr.level, params)) # copy the levels since we are changing them
        elif isinstance(expr, Const):
            return Const(cname=expr.cname, lvl_params=[substitute_level_params_level(l, params) for l in expr.lvl_params]) # copy the levels since we are changing them
        return None

    return replace_expression(body, replace_level_params)

def instantiate_bvar(body : Expression, val : Expression) -> Expression:
    """
    Replaces the outermost bound variable in the given expression with the given free variable. Throws an error if it finds an unbound bvar index.
    """
    def instantiation_fn(expr : Expression, depth : int) -> Optional[Expression]:
        if not expr.has_loose_bvars: return expr
        if isinstance(expr, BVar): 
            if expr.db_index == depth: return val
        return None
    return replace_expression_w_depth(body, instantiation_fn, 0)

def instantiate_bvars(body : Expression, vals : Sequence[Expression]) -> Expression:
    """
    Replaces the outermost bound variables in the given expression with the given free variables. Throws an error if it finds an unbound bvar index.
    """
    def instantiation_fn(expr : Expression, depth : int) -> Optional[Expression]:
        if not expr.has_loose_bvars: return expr
        if isinstance(expr, BVar): 
            if expr.db_index >= depth: 
                if expr.db_index - depth < len(vals): return vals[expr.db_index - depth]
                else: raise ValueError(f"Unbound de Bruijn index {expr.db_index}")
        return None
    return replace_expression_w_depth(body, instantiation_fn, 0)

def abstract_bvar(body : Expression, fvar : FVar) -> Expression:
    # turns fvar into a bound variable with de Bruijn index depth
    assert not fvar.type.has_loose_bvars, f"Cannot abstract a free variable with a loose bound variable in its type: {fvar}"
    if fvar.val is not None:
        assert not fvar.val.has_loose_bvars, f"Cannot abstract a free variable with a loose bound variable in its value: {fvar}"
    def abstraction_fn(expr : Expression, depth : int) -> Optional[Expression]:
        if not expr.has_fvars: return expr
        if isinstance(expr, FVar):
            if expr is fvar:
                return BVar(db_index=depth)
        return None
    
    return replace_expression_w_depth(body, abstraction_fn, 0)

def abstract_multiple_bvars(fvars : List[FVar], body : Expression) -> Expression:
    for fvar in fvars:
        assert not fvar.type.has_loose_bvars, f"Cannot abstract a free variable with a loose bound variable in its type: {fvar}"
        if fvar.val is not None:
            assert not fvar.val.has_loose_bvars, f"Cannot abstract a free variable with a loose bound variable in its value: {fvar}"
    """ Abstracts multiple free variables in the given expression. """
    def replace_fn(expr : Expression, depth : int) -> Optional[Expression]:
        if not expr.has_fvars: return expr
        if isinstance(expr, FVar):
            for i, fvar in enumerate(fvars):
                if fvar is expr: return BVar(db_index=depth + i)
        return None
    return replace_expression_w_depth(body, replace_fn, 0)

def unfold_app(expr : Expression) -> Tuple[Expression, List[Expression]]:
    """ If expr is of form (... ((f a1) a2) ... an), returns f, [a1, a2, ..., an]. """
    fn, args = unfold_app_rev(expr)
    return fn, list(reversed(args))

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

def fold_apps(fn : Expression, args : List[Expression]) -> Expression:
    """ Folds a function and a list of arguments into a single application expression. """
    result = fn
    for arg in args:
        result = App(fn=result, arg=arg)
    return result

def level_zip(lvl_params : List[LevelParam], lvl_values : List[Level]) -> LevelSubList:
    """ Checks if the two lists of levels have the same length and zips them together. """
    if len(lvl_params) != len(lvl_values): raise ValueError("Found different number of level parameters.")
    return list(zip(lvl_params, lvl_values))

class ReductionStatus(Enum):
    NOT_EQUAL = 0
    EQUAL = 1
    CONTINUE = 2
    UNKNOWN = 3

def replace_bvars_by_fvar(expr : Expression, fvar_list : List[FVar]) -> Expression:
    if isinstance(expr, BVar):
        return fvar_list[-expr.db_index-1]
    elif isinstance(expr, App):
        return App(fn=replace_bvars_by_fvar(expr.fn, fvar_list), arg=replace_bvars_by_fvar(expr.arg, fvar_list))
    elif isinstance(expr, Lambda):
        domain = replace_bvars_by_fvar(expr.domain, fvar_list)
        fvar_list.append(FVar(expr.bname, domain, None, False))
        body = replace_bvars_by_fvar(expr.body, fvar_list)
        fvar_list.pop()
        return Lambda(bname=expr.bname, domain=domain, body=body)
    elif isinstance(expr, Pi):
        domain = replace_bvars_by_fvar(expr.domain, fvar_list)
        fvar_list.append(FVar(expr.bname, domain, None, False))
        codomain = replace_bvars_by_fvar(expr.codomain, fvar_list)
        fvar_list.pop()
        return Pi(bname=expr.bname, domain=domain, codomain=codomain)
    elif isinstance(expr, Let):
        domain = replace_bvars_by_fvar(expr.domain, fvar_list)
        val = replace_bvars_by_fvar(expr.val, fvar_list)
        fvar_list.append(FVar(expr.bname, domain, val, False))
        body = replace_bvars_by_fvar(expr.body, fvar_list)
        fvar_list.pop()
        return Let(bname=expr.bname, domain=domain, val=val, body=body)
    elif isinstance(expr, Proj):
        return Proj(sname=expr.sname, index=expr.index, expr=replace_bvars_by_fvar(expr.expr, fvar_list))
    elif isinstance(expr, NatLit):
        return expr
    elif isinstance(expr, StrLit):
        return expr
    elif isinstance(expr, Sort):
        return expr
    elif isinstance(expr, Const):
        return expr
    elif isinstance(expr, FVar):
        return expr
    else:
        raise ValueError(f"Unknown expression type {expr.__class__.__name__}")
    

