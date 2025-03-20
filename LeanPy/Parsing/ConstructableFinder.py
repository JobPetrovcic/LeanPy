from typing import Dict, List, Set, Type, Union
from LeanPy.Parsing.DoAllLibraryConstants import do_on_all_constants
from LeanPy.Structures.Environment.Declarations.Declaration import Declaration, Definition, Theorem, Opaque
from LeanPy.Structures.Expression.Expression import *
from LeanPy.Structures.Expression.ExpressionManipulation import rename_level_params_with_index
from LeanPy.Structures.Expression.Level import *
from LeanPy.Structures.Expression.Expression import *
from LeanPy.Structures.Name import Name, string_to_name
import json
from LeanPy.Parsing.MathlibConstants import basic_constants

sentence_only = True

def is_constructable_level_aux(l : Level, visited : Dict[int, bool], available_constructors : Set[Union[Type[Expression], Type[Level]]]) -> bool:
    """
    Auxiliary function for do_fn. Recursively applies the given function to the expression and its subexpressions. Caches the visited expressions to avoid exponential blowup.
    """
    key = id(l)
    if key in visited: return visited[key]

    if l.__class__ not in available_constructors:
        constructable = False
    else:
        assert not isinstance(l, LevelMax)
        if isinstance(l, LevelSucc):
            constructable = is_constructable_level_aux(l.anc, visited, available_constructors)
        elif isinstance(l, LevelMax):
            constructable = is_constructable_level_aux(l.lhs, visited, available_constructors) and is_constructable_level_aux(l.rhs, visited, available_constructors)
        elif isinstance(l, LevelIMax):
            constructable = is_constructable_level_aux(l.lhs, visited, available_constructors) and is_constructable_level_aux(l.rhs, visited, available_constructors)
        else:
            constructable = True

    visited[key] = constructable
    return constructable

def is_constructable_level(l : Level, available_constructors : Set[Union[Type[Expression], Type[Level]]]) -> bool:
    return is_constructable_level_aux(l, dict(), available_constructors)

def find_constructable_aux(e : Expression, visited : Dict[int, bool], constructable_hashes : Dict[int, Expression], available_constructors : Set[Union[Type[Expression], Type[Level]]],  available_constants : Set[Name]) -> bool:
    """
    Auxiliary function for do_fn. Recursively applies the given function to the expression and its subexpressions. Caches the visited expressions to avoid exponential blowup.
    """
    key = id(e)
    if key in visited: return visited[key]

    if e.__class__ not in available_constructors:
        constructable = False
    else:
        if isinstance(e, Const):
            constructable = e.cname in available_constants
            for lvl in e.lvl_params:
                constructable = constructable and is_constructable_level(lvl, available_constructors)
        elif isinstance(e, Sort):
            constructable = is_constructable_level(e.level, available_constructors)
        elif isinstance(e, App):
            constructable = find_constructable_aux(e.fn, visited, constructable_hashes, available_constructors, available_constants) and find_constructable_aux(e.arg, visited, constructable_hashes, available_constructors, available_constants)
        elif isinstance(e, Lambda):
            constructable = find_constructable_aux(e.domain, visited, constructable_hashes, available_constructors, available_constants) and find_constructable_aux(e.body, visited, constructable_hashes, available_constructors, available_constants)
        elif isinstance(e, Pi):
            constructable = find_constructable_aux(e.domain, visited, constructable_hashes, available_constructors, available_constants) and find_constructable_aux(e.codomain, visited, constructable_hashes, available_constructors, available_constants)
        elif isinstance(e, Let):
            constructable = find_constructable_aux(e.domain, visited, constructable_hashes, available_constructors, available_constants) and find_constructable_aux(e.val, visited, constructable_hashes, available_constructors, available_constants) and find_constructable_aux(e.body, visited, constructable_hashes, available_constructors, available_constants)
        elif isinstance(e, Proj):
            constructable = find_constructable_aux(e.expr, visited, constructable_hashes, available_constructors, available_constants)
        else:
            constructable = True
    if constructable and ((not sentence_only) or (not e.has_loose_bvars)):
        e_hash = hash(e)
        if e_hash in constructable_hashes and constructable_hashes[e_hash] != e:
            print(f"Hash collision: {constructable_hashes[e_hash]} and {e}")
        constructable_hashes[e_hash] = e

    visited[key] = constructable
    return constructable

def find_constructable(e : Expression, constructable_hashes : Dict[int, Expression], available_constructors : Set[Union[Type[Expression], Type[Level]]], available_constants : Set[Name]) -> bool:
    return find_constructable_aux(e, dict(), constructable_hashes, available_constructors, available_constants)

if __name__ == "__main__":
    import sys
    sys.setrecursionlimit(10**9)

    dir = "/home/jp/projects/Mathlib4Extraction/mathlib4/json_dump"

    available_constructors : Set[Union[Type[Expression], Type[Level]]] = set([
        LevelZero,
        LevelSucc,
        #LevelMax,
        #LevelIMax,
        LevelParam,

        Const, 
        App,
        Lambda,
        Pi,
        Let,
        Proj,
        BVar,
        Sort,
        #NatLit,
        #StrLit,
    ])

    available_constants = set([
        string_to_name(const)
        for const in basic_constants
    ])

    constructable_data : Dict[str, List[int]] = {}
    all_found_constructable_hashes : Set[int] = set()

    def get_constructable_hashes_from_decl(name: str, deps: List[str], decl: Declaration):
        global all_found_constructable_hashes
        constructable_hashes: Dict[int, Expression] = {}
        find_constructable(decl.type, constructable_hashes, available_constructors, available_constants)
        if hasattr(decl, "value"):
            assert isinstance(decl, Definition) or isinstance(decl, Theorem) or isinstance(decl, Opaque)
            find_constructable(decl.value, constructable_hashes, available_constructors, available_constants)

        for value in constructable_hashes.values():
            e_with_params_renamed = rename_level_params_with_index(value, dict())
            key = hash(e_with_params_renamed)
            if key not in all_found_constructable_hashes:
                all_found_constructable_hashes.add(key)
                print(f"Found new constructable hash: {e_with_params_renamed} with hash {key}")
        
        constructable_data[name] = list(constructable_hashes.keys())

    do_on_all_constants(
        dir=dir,
        fn=get_constructable_hashes_from_decl
    )

    with open("constructable_hashes_sentences_only.json", "w") as f:
        json.dump(constructable_data, f, indent=2)