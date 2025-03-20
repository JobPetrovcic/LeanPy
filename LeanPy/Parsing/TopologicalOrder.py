
import os
import sys
import pickle
from typing import List, Set
from LeanPy.Parsing.LeanJSONParser import from_file

sys.setrecursionlimit(100000)


def find_topological_order(dir : str, save_path : str):
    visited : Set[str] = set()
    order : List[str] = []

    def dfs(node : str):
        if node in visited:
            return
        visited.add(node)
        dependencies, decl = from_file(f"{dir}/{node}.json")

        for dep in dependencies:
            dfs(dep)
        order.append(node)
        print(f"{node} ({decl.__class__.__name__}): {dependencies}")

    for file in os.listdir(dir):
        if file.endswith(".json"):
            dfs(file[:-5])

    with open(save_path, "wb") as f:
        pickle.dump(order, f)
        
if __name__ == "__main__":
    dir = "/home/jp/projects/Mathlib4Extraction/mathlib4/json_dump"
    find_topological_order(dir, "topological_order.pkl")