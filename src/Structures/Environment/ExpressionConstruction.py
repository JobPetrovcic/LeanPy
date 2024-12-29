from typing import List, Tuple

from Structures.Expression.Expression import Expression, FVar, Pi, Sort
from Structures.Expression.ExpressionManipulation import abstract_bvar, has_fvars
from Structures.Expression.Level import LevelParam
from Structures.Name import Name, SubName

named_expression = Tuple[Name | None, Expression]

def create_level_param(anc : Name, name_end : str) -> LevelParam:
    name = SubName(anc, name_end)
    return LevelParam(name)
    
def create_sort_param(anc : Name, name_end : str) -> Tuple[LevelParam, Expression]:
    level_param = create_level_param(anc, name_end)
    return level_param, Sort(level_param)

def create_named_fvar(anc : Name, name_end : str, type : Expression) -> named_expression:
    name = SubName(anc, name_end)
    return (name, FVar(name, type, None, False))

def create_arrow_type_aux(binders : List[named_expression], body : Expression, last_name : Name, anonymous_arg_count : int = 0) -> Expression:
    """Given a list of named expressions and a body, create a with binder belonging to the named expression, arg_types the expression and body_type the body"""
    if len(binders) == 0:
        return body
    
    rest = binders[1:]
    is_fvar = False
    exp = binders[0][1]
    if binders[0][0] is not None: 
        c_binder = binders[0][0]
        assert isinstance(exp, FVar)
        last_name = c_binder
        is_fvar = True
    else:
        # anonymous name
        c_binder = SubName(last_name, "_anon_arg" + str(anonymous_arg_count))
        anonymous_arg_count += 1
    
    result = Pi(bname=c_binder, arg_type=exp, body_type=create_arrow_type_aux(rest, body, last_name, anonymous_arg_count))
    if is_fvar:
        assert isinstance(exp, FVar)
        result = abstract_bvar(result, exp, False, True)
    return result

def create_arrow_type(binders : List[named_expression], body : Expression, namespace : Name) -> Expression:
    result = create_arrow_type_aux(binders, body, namespace)
    assert not has_fvars(result)
    return result
