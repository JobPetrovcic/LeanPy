import sys
from typing import Type
#import matplotlib.pyplot as plt
import tqdm
from LeanPy.Parsing.DoAllLibraryConstants import do_on_all_constants
from LeanPy.Parsing.LeanJSONParser import *
from LeanPy.Structures.Expression.ExpressionManipulation import do_fn, do_fn_w_depth
from LeanPy.Structures.Expression.LevelManipulation import do_fn_level
import csv

sys.setrecursionlimit(10**9)

def count_unique_level_nodes(l : Level):
    count_level = 0
    def count_fn(l : Level):
        nonlocal count_level
        count_level += 1

    do_fn_level(l, count_fn)
    return count_level

def count_unique_nodes(e : Expression) -> tuple[int, int]:
    count_expr = 0
    count_level = 0
    def count_fn(e : Expression):
        nonlocal count_expr
        nonlocal count_level
        count_expr += 1 
        if isinstance(e, Sort):
            count_level += count_unique_level_nodes(e.level)
        elif isinstance(e, Const):
            for lvl in e.lvl_params:
                count_level += count_unique_level_nodes(lvl)

    do_fn(e, count_fn)
    return count_expr, count_level

def get_indegrees(dir : str) -> Dict[str, int]:
    indegrees : Dict[str, int] = {}
    def count_fn(file_name : str, dependencies : List[str], declaration : Declaration):
        for dep in dependencies:
            indegrees[dep] = indegrees.get(dep, 0) + 1

    do_on_all_constants(dir, count_fn)
    return indegrees

def get_used_constants(e : Expression) -> Dict[Name, int]:
    used_constants : Dict[Name, int] = {}
    def count_fn(e : Expression):
        if isinstance(e, Const):
            used = used_constants.get(e.cname, 0)
            used_constants[e.cname] = used + 1
    
    do_fn(e, count_fn)
    return used_constants

def depth_fn_aux(e : Expression, visited : Dict[int, int]) -> int:
    """
    Auxiliary function for do_fn. Recursively applies the given function to the expression and its subexpressions. Caches the visited expressions to avoid exponential blowup.
    """
    key = id(e)
    if key in visited: return visited[key]
    
    if isinstance(e, App):
        depth = max(depth_fn_aux(e.fn, visited), depth_fn_aux(e.arg, visited)) + 1
    elif isinstance(e, Lambda):
        depth = max(depth_fn_aux(e.domain, visited), depth_fn_aux(e.body, visited)) + 1
    elif isinstance(e, Pi):
        depth = max(depth_fn_aux(e.domain, visited), depth_fn_aux(e.codomain, visited)) + 1
    elif isinstance(e, Let):
        depth = max(depth_fn_aux(e.domain, visited), depth_fn_aux(e.val, visited), depth_fn_aux(e.body, visited)) + 1
    elif isinstance(e, Proj):
        depth = depth_fn_aux(e.expr, visited) + 1
    else:
        depth = 1
    visited[key] = depth
    return depth

def depth_fn(e : Expression):
    return depth_fn_aux(e, dict())

class LibraryStatistics:
    def __init__(self, constants_freq : Dict[Name, int]):
        self.constants_freq = constants_freq
    
    @staticmethod
    def to_csv(ls: 'LibraryStatistics', file: str):
        with open(file, "w", newline="") as csvfile:
            writer = csv.writer(csvfile)
            writer.writerow(["constant", "frequency"])
            for constant, freq in ls.constants_freq.items():
                writer.writerow([str(constant), freq])

class DeclarationStatistics:
    def __init__(self, 
            file_name : str,
            decl_class : Type[Declaration],
            constructor_count_type: Dict[Type[Expression] | Type[Level], int], 
            constructor_count_value: Dict[Type[Expression] | Type[Level], int] | None,
            additional_constructors_levels_count_type: Dict[str, int],
            additional_constructors_levels_count_value: Dict[str, int] | None,
            root_depth_type: int,
            root_depth_value: int | None,
            context_lens_type: Dict[int, int], 
            context_lens_value: Dict[int, int] | None,
            leaf_count_type: int,
            leaf_count_value: int | None
        ):
        assert (constructor_count_value is None) == (root_depth_value is None) == (context_lens_value is None) == (leaf_count_value is None)

        self.file_name = file_name
        self.decl_class = decl_class
        self.constructor_count_type = constructor_count_type
        self.constructor_count_value = constructor_count_value
        self.additional_constructors_levels_count_type = additional_constructors_levels_count_type
        self.additional_constructors_levels_count_value = additional_constructors_levels_count_value
        self.root_depth_type = root_depth_type
        self.root_depth_value = root_depth_value
        self.context_lens_type = context_lens_type
        self.context_lens_value = context_lens_value
        self.leaf_count_type = leaf_count_type
        self.leaf_count_value = leaf_count_value

    all_constructor_types: List[Type[Expression] | Type[Level]] = [
        LevelZero, LevelSucc, LevelMax, LevelIMax, LevelParam, 
        App, Lambda, Pi, Let, Const, BVar, Sort, Proj, NatLit, StrLit
    ]
    additional_constructors_levels: Dict[str, Level] = {
        "LevelOne": LevelSucc(LevelZero()),
        "LevelTwo": LevelSucc(LevelSucc(LevelZero())),
    }
    
    @staticmethod
    def to_csv(dss: List['DeclarationStatistics'], file: str):
        # Build header list
        header : List[str] = []
        header.extend(["file_name"])
        header.append("decl_class")
        header.extend([f"type_{constructor.__name__}" for constructor in DeclarationStatistics.all_constructor_types])
        header.extend([f"value_{constructor.__name__}" for constructor in DeclarationStatistics.all_constructor_types])
        header.extend([f"type_{constructor_name}" for constructor_name in DeclarationStatistics.additional_constructors_levels.keys()])
        header.extend([f"value_{constructor_name}" for constructor_name in DeclarationStatistics.additional_constructors_levels.keys()])
        header.extend(["root_depth_type", "root_depth_value"])
        header.extend(["context_len_type", "context_len_value"])
        header.extend(["leaf_count_type", "leaf_count_value"])

        with open(file, "w", newline="") as csvfile:
            writer = csv.writer(csvfile)
            writer.writerow(header)
            for ds in tqdm.tqdm(dss):
                row : List[str| int] = []

                # File name
                row.append(ds.file_name)

                # type of declaration
                row.append(ds.decl_class.__name__)

                # Constructor counts for type
                row.extend([ds.constructor_count_type.get(constructor, 0) for constructor in DeclarationStatistics.all_constructor_types])
                row.extend([ds.additional_constructors_levels_count_type.get(constructor_name, 0) for constructor_name in DeclarationStatistics.additional_constructors_levels.keys()])
                # Constructor counts for value
                if ds.constructor_count_value is not None:
                    row.extend([ds.constructor_count_value.get(constructor, 0) for constructor in DeclarationStatistics.all_constructor_types])
                    assert ds.additional_constructors_levels_count_value is not None
                    row.extend([ds.additional_constructors_levels_count_value.get(constructor_name, 0) for constructor_name in DeclarationStatistics.additional_constructors_levels.keys()])
                else:
                    row.extend(["" for _ in DeclarationStatistics.all_constructor_types])
                # Root depths
                row.append(ds.root_depth_type)
                row.append(ds.root_depth_value if ds.root_depth_value is not None else "")

                # Context lengths for type
                row.append(max(ds.context_lens_type.keys(), default=0))
                # Context lengths for value
                if ds.context_lens_value is not None:
                    row.append(max(ds.context_lens_value.keys(), default=0))
                else:
                    row.append("")

                # Leaf counts
                row.append(ds.leaf_count_type)
                row.append(ds.leaf_count_value if ds.leaf_count_value is not None else "")
                assert len(row) == len(header)
                writer.writerow(row)

def statistics_expression_fn(e : Expression):
    constructor_count : Dict[Type[Expression] | Type[Level], int] = {}
    additional_constructors_levels_count: Dict[str, int] = {}
    context_lens : Dict[int, int] = {}
    leaf_count = 0

    def extract_statistics_level_fn(l : Level):
        constructor_count[type(l)] = constructor_count.get(type(l), 0) + 1
        for constructor_name, constructor_level in DeclarationStatistics.additional_constructors_levels.items():
            if l == constructor_level:
                additional_constructors_levels_count[constructor_name] = additional_constructors_levels_count.get(constructor_name, 0
                ) + 1
        
    def extract_statistics_fn(e : Expression, depth : int):
        nonlocal leaf_count
        context_lens[depth] = context_lens.get(depth, 0) + 1
        constructor_count[type(e)] = constructor_count.get(type(e), 0) + 1
        if isinstance(e, Const) or isinstance(e, BVar) or isinstance(e, Sort) or isinstance(e, NatLit) or isinstance(e, StrLit):
            leaf_count += 1

        if isinstance(e, Sort):
            do_fn_level(e.level, extract_statistics_level_fn)
        elif isinstance(e, Const):
            for lvl in e.lvl_params:
                do_fn_level(lvl, extract_statistics_level_fn)
    
    root_depth = depth_fn(e)
    do_fn_w_depth(e, extract_statistics_fn)

    used_constants = get_used_constants(e)

    return constructor_count, additional_constructors_levels_count, root_depth, context_lens, leaf_count, used_constants

def get_basic_statistics(dir : str):
    statistics_list : List[DeclarationStatistics] = []
    used_constants_all : Dict[Name, int] = {}
    def statistics_fn(file_name : str, dependencies : List[str], declaration : Declaration):
        constructor_count_type, additional_constructors_levels_count_type, root_depth_type, context_lens_type, leaf_count_type, used_constants_type = statistics_expression_fn(declaration.type)
        for constant, count in used_constants_type.items():
            used_constants_all[constant] = used_constants_all.get(constant, 0) + count
        if hasattr(declaration, "value"):
            assert isinstance(declaration, (Definition, Theorem, Opaque))
            constructor_count_value, additional_constructors_levels_count_value, root_depth_value, context_lens_value, leaf_count_value, used_constants_value = statistics_expression_fn(declaration.value)
            for constant, count in used_constants_value.items():
                used_constants_all[constant] = used_constants_all.get(constant, 0) + count
        else:
            constructor_count_value, additional_constructors_levels_count_value, root_depth_value, context_lens_value, leaf_count_value = None, None, None, None, None
        
        ds = DeclarationStatistics(
            file_name,
            type(declaration),
            constructor_count_type, 
            constructor_count_value,
            additional_constructors_levels_count_type,
            additional_constructors_levels_count_value,
            root_depth_type,
            root_depth_value,
            context_lens_type,
            context_lens_value,
            leaf_count_type,
            leaf_count_value
        )
        statistics_list.append(ds)

    do_on_all_constants(dir, statistics_fn)

    library_statistics = LibraryStatistics(used_constants_all)
    return statistics_list, library_statistics

if __name__ == "__main__":
    dir = "/home/jp/projects/Mathlib4Extraction/mathlib4/json_dump"
    declaration_statistics_file = "Statistics/statistics.csv"
    library_statistics_file = "Statistics/library_statistics.csv"

    statistics, library_statistics = get_basic_statistics(dir)
    DeclarationStatistics.to_csv(statistics, declaration_statistics_file)
    LibraryStatistics.to_csv(library_statistics, library_statistics_file)

#if __name__ == "__main__":
#    dir = "/home/jp/projects/Mathlib4Extraction/mathlib4/json_dump"
#    indegree_file = "Statistics/indegree.txt"
#    indegrees = get_indegrees(dir)
#
#    # sort the constants by indegree and write them to a file
#    sorted_indegrees = sorted(indegrees.items(), key=lambda x: x[1], reverse=True)
#    with open(indegree_file, "w") as f:
#        for constant, indegree in sorted_indegrees:
#            f.write(f"{constant}: {indegree}\n")

#def plot(list_file : str):
#    # read the file which contains two lists
#    with open(list_file, "r") as f:
#        lists = f.readlines()
#        # the lists are strings of the form "[1, 2, 3, 4, 5]\n"
#        type_sizes = list(map(int, lists[0][1:-2].split(", ")))
#        value_sizes = list(map(int, lists[1][1:-2].split(", ")))
#
#    # Plotting
#    # determine the bin size dynamically
#    bin_size = max(max(type_sizes), max(value_sizes)) // 10000
#    bins = range(0, max(max(type_sizes), max(value_sizes)) + bin_size, bin_size)
#    plt.hist(type_sizes, bins=bins, alpha=0.5, label="Type", log=True)
#    plt.hist(value_sizes, bins=bins, alpha=0.5, label="Value", log=True)
#    plt.xscale("log")
#    plt.legend(loc='upper right')
#    plt.xlabel("Number of unique nodes")
#    plt.ylabel("Number of declarations (log scale)")
#    plt.title("Number of unique nodes in the type and the values expressions")
#    
#    # save the plot
#    plt.savefig("number_of_unique_nodes.png")
#
#if __name__ == "__main__":
#    dir = "/home/jp/projects/Mathlib4Extraction/mathlib4/json_dump"
#    sizes_file = "LeanPy/Parsing/sizes.txt"
#
#    # if the file already exists, plot it
#    if not os.path.exists(sizes_file):
#        type_sizes : List[int] = []
#        value_sizes : List[int] = []
#        for file in tqdm.tqdm(os.listdir(dir)):
#            if file.endswith(".json"):
#                dependencies, declaration = from_file(f"{dir}/{file}")
#
#                type_size_expr, type_size_lvl = count_unique_nodes(declaration.type)
#                type_sizes.append(type_size_expr + type_size_lvl)
#                if hasattr(declaration, "value"):
#                    value_size_expr, value_size_lvl = count_unique_nodes(declaration.value)
#                    value_sizes.append(value_size_expr + value_size_lvl)
#        
#        with open(sizes_file, "w") as f:
#            f.write(type_sizes)
#            f.write("\n")
#            f.write(value_sizes)
#    
#    plot(sizes_file)