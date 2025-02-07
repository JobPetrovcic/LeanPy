import os
import pickle
from typing import List, Set

import tqdm

from LeanPy.Kernel.TypeChecker import TypeChecker
from LeanPy.Parsing import LeanJSONParser
from LeanPy.Structures.Environment.Declarations.Declaration import Declaration

class DependencyManager:
    def __init__(self, folder : str, already_checked_file_path : str | None = None):
        """
        The DependencyManager class is responsible for managing the dependencies of declarations. The declaration can be in the following states:
        - Not loaded
        - Loaded
        - Loaded and all of the dependencies are loaded (recursively)
        - Loading: its dependencies are being loaded, but it it might or might not be loaded
        - Checked (also loaded and all of the dependencies are loaded)
        """
        self.folder = folder
        self.already_checked_file_path = already_checked_file_path
        self.type_checker = TypeChecker()

        self.loaded : Set[str] = set()
        self.loading : Set[str] = set()
        self.loaded_and_dependencies_loaded : Set[str] = set()
        self.checked : Set[str] = set()
        self.being_checked : Set[str] = set()
        self.file_name_to_dependencies : dict[str, List[str]] = {}
        self.file_name_to_declaration : dict[str, Declaration] = {}

        if already_checked_file_path is not None:
            # if the file exists, load it
            if os.path.exists(already_checked_file_path):
                with open(already_checked_file_path, "rb") as f:
                    self.already_checked = pickle.load(f)
                for decl_file_name in self.already_checked:
                    self.load_and_load_dependencies(decl_file_name)
            else:
                self.already_checked : Set[str] = set()
        else:
            self.already_checked : Set[str] = set()

    def is_checked(self, decl_file_name : str) -> bool:
        """
        Returns whether the declaration has been checked.
        """
        return decl_file_name in self.checked

    def load(self, decl_file_name: str):
        # Ensure the declaration is marked as loading before processing
        if decl_file_name not in self.loading:
            self.loading.add(decl_file_name)
        if decl_file_name in self.loaded:
            raise Exception(f"Declaration {decl_file_name} already loaded")
        assert decl_file_name in self.loading, f"Declaration {decl_file_name} not loading"
        assert decl_file_name not in self.file_name_to_declaration, f"Declaration {decl_file_name} already in file_name_to_declaration"
        
        dependencies, declaration = LeanJSONParser.from_file(os.path.join(self.folder, f"{decl_file_name}.json"))
        self.file_name_to_declaration[decl_file_name] = declaration
        self.file_name_to_dependencies[decl_file_name] = dependencies
        if self.type_checker.environment.exists_declaration_under_name(declaration.name):
            raise Exception(f"Declaration {declaration.name} already in environment")
        self.type_checker.environment.add_declaration(declaration)
        self.loaded.add(decl_file_name)

        return dependencies, declaration
    
    def load_and_load_dependencies(self, decl_file_name : str):
        if decl_file_name in self.loading:
            raise Exception(f"Declaration {decl_file_name} already loading")
        if decl_file_name in self.loaded_and_dependencies_loaded:
            return self.file_name_to_dependencies[decl_file_name], self.file_name_to_declaration[decl_file_name]

        self.loading.add(decl_file_name)
        if decl_file_name in self.loaded:
            dependencies = self.file_name_to_dependencies[decl_file_name]
            declaration = self.file_name_to_declaration[decl_file_name]
        else:
            dependencies, declaration = self.load(decl_file_name)

        for dependency in dependencies:
            if dependency not in self.loaded and dependency not in self.loading and dependency not in self.loaded_and_dependencies_loaded:
                self.load_and_load_dependencies(dependency)

        self.loaded_and_dependencies_loaded.add(decl_file_name)
        self.loading.remove(decl_file_name)

        return dependencies, declaration
    
    def check(self, decl_file_name : str):
        declaration = self.file_name_to_declaration[decl_file_name]
        self.type_checker.check_declaration(declaration)
        self.checked.add(decl_file_name)

    def load_and_check(
            self, 
            decl_file_name : str,
            is_main : bool = True,
            should_dependencies_be_checked : bool = True,
        ):
        if decl_file_name in self.checked:
            raise Exception(f"Declaration {decl_file_name} already checked")
        if decl_file_name in self.being_checked:
            raise Exception(f"Declaration {decl_file_name} already being checked")
        
        self.being_checked.add(decl_file_name)
        dependencies, _ = self.load_and_load_dependencies(decl_file_name)

        if should_dependencies_be_checked:
            for dependency in dependencies:
                if dependency not in self.checked and dependency not in self.being_checked:
                    self.load_and_check(dependency, is_main = False, should_dependencies_be_checked = should_dependencies_be_checked)

        if decl_file_name in self.loading:
            raise Exception(f"Declaration {decl_file_name} still loading. This should be unreachable.")
        if decl_file_name not in self.loaded:
            raise Exception(f"Declaration {decl_file_name} not loaded. This should be unreachable.")
        if decl_file_name not in self.loaded_and_dependencies_loaded:
            raise Exception(f"Declaration {decl_file_name} not loaded and all dependencies loaded. This should be unreachable.")
        if decl_file_name not in self.file_name_to_declaration:
            raise Exception(f"Declaration {decl_file_name} not in file_name_to_declaration")
        
        should_check = is_main or should_dependencies_be_checked
        if should_check:
            self.check(decl_file_name)
            self.save_checked()
        
        self.being_checked.remove(decl_file_name)

    def save_checked(self):
        if (len(self.checked) + 1) % 100 == 0 and self.already_checked_file_path is not None:
            with open(self.already_checked_file_path, "wb") as f:
                pickle.dump(self.checked, f)

    def __len__(self):
        return len(self.file_name_to_declaration)
    
    def __total__(self):
        """
        Returns the number of files in the folder that end with ".json"
        """
        return len([f for f in os.listdir(self.folder) if f.endswith(".json")])

    def update_tqdm(self, tqdm_instance : tqdm.tqdm):
        tqdm_instance.total = self.__total__()
        tqdm_instance.n = len(self)
        tqdm_instance.refresh()
        