import os
import pickle
from typing import Dict, List, Set

from LeanPy.Kernel.TypeChecker import TypeChecker
from LeanPy.Parsing import LeanJSONParser
from LeanPy.Structures.Environment.Declarations.Declaration import Declaration
from LeanPy.Structures.Environment.Environment import Environment

n_to_save_already_checked = 100
already_checked_file_path = "already_checked.pickle"

class DependencyManager:
    def __init__(self, folder : str, save_already_checked : bool = False):
        # we keep track of which files have been loaded
        # NOTE: name of the declaration don't match the file name
        # currently, the only differnce is that "/" -> " "
        self.already_checked : Set[str] = set()
        if save_already_checked and (already_checked_file_path in os.listdir()):
            self.already_checked = pickle.load(open(already_checked_file_path, "rb"))
            print(f"Loaded {len(self.already_checked)} already checked files")
        self.save_already_checked = save_already_checked

        self.loaded : Dict[str, bool] = {}
        self.loading : Set[str] = set()
        self.environment = Environment()
        self.type_checker = TypeChecker()
        self.folder = folder

    def is_loaded(self, decl_file_name : str) -> bool:
        return decl_file_name in self.loaded

    def check_dependencies_loaded(self, dependencies : List[str]) -> bool:
        for dependency in dependencies:
            if dependency not in self.loaded:
                return False
        return True
    
    def load_isolated(self, decl_file_name : str, declaration : Declaration, type_check : bool = True):
        if decl_file_name in self.loaded:
            raise Exception(f"Dependency {decl_file_name} already loaded")
        self.loaded[decl_file_name] = True
        
        self.type_checker.local_context.clear()
        
        type_check = type_check and not (decl_file_name in self.already_checked)

        self.type_checker.add_declaration(decl=declaration, type_check=type_check)

        if decl_file_name not in self.already_checked:
            self.already_checked.add(decl_file_name)
            if self.save_already_checked and (len(self.already_checked) % n_to_save_already_checked) == 0:
                pickle.dump(self.already_checked, open(already_checked_file_path, "wb"))

    def load(self, decl_file_name : str, is_main : bool = True, type_check_dependencies : bool = True):
        """
        Same as load_isolated, but also loads all dependencies
        """
        if decl_file_name in self.loaded:
            return

        if decl_file_name in self.loading:
            raise Exception(f"Dependency {decl_file_name} already loading")
        self.loading.add(decl_file_name)
        
        print(f"Loading {decl_file_name}")
        dependecies, declaration = LeanJSONParser.from_file(self.folder + "/" + decl_file_name + ".json")
        for dependency in dependecies:
            if dependency not in self.loaded and dependency not in self.loading:
                self.load(dependency, False, type_check_dependencies)

        self.check_dependencies_loaded(dependecies)
        
        self.load_isolated(decl_file_name, declaration, is_main or type_check_dependencies)

        self.loading.remove(decl_file_name)