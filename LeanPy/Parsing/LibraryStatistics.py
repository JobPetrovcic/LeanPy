import os
import sys
import matplotlib.pyplot as plt
import tqdm
from LeanPy.Parsing.LeanJSONParser import *
from LeanPy.Structures.Expression.ExpressionManipulation import do_fn
from LeanPy.Structures.Expression.LevelManipulation import do_fn_level

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

def plot(list_file : str):
    # read the file which contains two lists
    with open(list_file, "r") as f:
        lists = f.readlines()
        # the lists are strings of the form "[1, 2, 3, 4, 5]\n"
        type_sizes = list(map(int, lists[0][1:-2].split(", ")))
        value_sizes = list(map(int, lists[1][1:-2].split(", ")))

    # Plotting
    # determine the bin size dynamically
    bin_size = max(max(type_sizes), max(value_sizes)) // 10000
    bins = range(0, max(max(type_sizes), max(value_sizes)) + bin_size, bin_size)
    plt.hist(type_sizes, bins=bins, alpha=0.5, label="Type", log=True)
    plt.hist(value_sizes, bins=bins, alpha=0.5, label="Value", log=True)
    plt.xscale("log")
    plt.legend(loc='upper right')
    plt.xlabel("Number of unique nodes")
    plt.ylabel("Number of declarations (log scale)")
    plt.title("Number of unique nodes in the type and the values expressions")
    
    # save the plot
    plt.savefig("number_of_unique_nodes.png")

if __name__ == "__main__":
    dir = "/home/jp/projects/Mathlib4Extraction/mathlib4/json_dump"
    sizes_file = "LeanPy/Parsing/sizes.txt"

    # if the file already exists, plot it
    if not os.path.exists(sizes_file):
        type_sizes : List[int] = []
        value_sizes : List[int] = []
        for file in tqdm.tqdm(os.listdir(dir)):
            if file.endswith(".json"):
                dependencies, declaration = from_file(f"{dir}/{file}")

                type_size_expr, type_size_lvl = count_unique_nodes(declaration.type)
                type_sizes.append(type_size_expr + type_size_lvl)
                if hasattr(declaration, "value"):
                    value_size_expr, value_size_lvl = count_unique_nodes(declaration.value)
                    value_sizes.append(value_size_expr + value_size_lvl)
        
        with open(sizes_file, "w") as f:
            f.write(type_sizes)
            f.write("\n")
            f.write(value_sizes)
    
    plot(sizes_file)


                
            
