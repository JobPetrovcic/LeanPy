import json
from typing import Any, List, Tuple



from LeanPy.Structures.Name import *
from LeanPy.Structures.Expression.Level import * 
tag_to_level_class = {c.__name__ : c for c in level_constructors}

from LeanPy.Structures.Expression.Expression import *
tag_to_expr_class = {c.__name__ : c for c in expr_constructors}

from LeanPy.Structures.Environment.Declaration.Declaration import *
from LeanPy.Structures.Environment.ReducibilityHint import *

from typing import Union, Dict

json_type = Union[str, int, list['json_type'], dict[str, 'json_type']]

#@typechecked
def getObj(tag : str, args : Dict[str, Any]) -> Any:
    return globals()[tag](**args)

#@typechecked
def deserialize_expr(json_obj : dict[str, 'json_type'], subexprs : List[Expression | None]) -> Union[Expression, Level]:
    tag = json_obj['tag']
    assert isinstance(tag, str), f"Expected string, got {tag}"
    assert tag in tag_to_expr_class or (tag == 'ExprRef'), f"Expected expression tag, got {tag}"

    # this avoids exponential blowup: if an expression was already created, return it
    if tag == 'ExprRef':
        assert isinstance(json_obj['ei'], int), f"Expected int, got {json_obj['ei']}"
        got = subexprs[json_obj['ei']]
        assert got is not None, f"Expected non-None expression at index {json_obj['ei']}"
        return got
    
    args = json_obj['args']
    assert isinstance(args, dict), f"Expected dictionary, got {args}"

    # check that the index is correct
    ind = json_obj['ei']
    assert isinstance(ind, int), f"Expected int, got {ind}"

    assert len(subexprs) == ind, f"Expected {ind} but got {len(subexprs)} when deserializing {json_obj}"
    subexprs.append(None)

    # a new expression or level is created
    # go through the arguments and deserialize them
    for k, v in args.items(): args[k] = deserialize_json(v, subexprs)

    # create the object using the deserialized arguments
    obj = getObj(tag, args)

    assert subexprs[ind] is None, f"Expected None at index {ind}, got {subexprs[ind]}"
    subexprs[ind] = obj
    return obj

#@typechecked
def deserialize_list(json_list : List[json_type], subexprs : List[Expression | None] | None): return [deserialize_json(x, subexprs) for x in json_list]

#@typechecked
def deserialize_json(json_obj : json_type, subexprs_or_none : List[Expression | None] | None ) -> Any:
    if isinstance(json_obj, list): return deserialize_list(json_obj, subexprs_or_none)
    elif isinstance(json_obj, dict): 
        tag = json_obj['tag']
        assert isinstance(tag, str), f"Expected string, got {tag}"
        
        if (tag in tag_to_expr_class) or tag == 'ExprRef': 
            if subexprs_or_none is None: 
                subexprs = []
            else:
                subexprs = subexprs_or_none

            return deserialize_expr(json_obj, subexprs)
        
        args = json_obj['args']
        assert isinstance(args, dict), f"Expected dictionary, got {args}"
        for k, v in args.items(): args[k] = deserialize_json(v, subexprs_or_none)
        return getObj(tag, args)
    elif isinstance(json_obj, str): return json_obj
    elif isinstance(json_obj, int): return json_obj # type: ignore
    else: raise ValueError(f"Unexpected JSON object: {json_obj}")

def deserialize_declaration_profile(json_obj : json_type) -> Tuple[List[str], Declaration]:
    # the initial json object is a dictionary with two keys: dependencies and json-ed content of the declaration
    assert isinstance(json_obj, dict), f"Expected dictionary, got {json_obj}"
    raw_dependencies = json_obj['dependencies']
    # check that dependencies is a list of strings
    assert isinstance(raw_dependencies, list), f"Expected list, got {raw_dependencies}"
    dependencies : List[str] = []
    for dep in raw_dependencies: 
        assert isinstance(dep, str)
        dependencies.append(dep)

    declaration_content = json_obj['content']
    return dependencies, deserialize_json(declaration_content, None)

def from_file(file_path : str) -> Tuple[List[str], Declaration]:
    # assert that the file is a json file
    assert file_path.endswith('.json'), f"Expected JSON file, got {file_path}"
    with open(file_path, 'r') as f:
        json_object = json.load(f)
        return deserialize_declaration_profile(json_object)