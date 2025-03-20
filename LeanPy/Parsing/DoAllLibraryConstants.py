

import os
from typing import Callable, List

import tqdm

from LeanPy.Parsing.LeanJSONParser import from_file
from LeanPy.Structures.Environment.Declarations.Declaration import Declaration

def do_on_all_constants(dir : str, fn : Callable[[str, List[str], Declaration], None]):
    for file in tqdm.tqdm(os.listdir(dir)):
        if file.endswith(".json"):
            dependencies, declaration = from_file(f"{dir}/{file}")
            fn(file[:-5], dependencies, declaration)

