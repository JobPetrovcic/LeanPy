import os
from typing import List, Tuple

from LeanPy.Kernel.TypeChecker import TypeChecker
from LeanPy.Parsing import LeanJSONParser
from LeanPy.Structures.Environment.Declarations.Declaration import Declaration, Definition, Theorem, Opaque
from LeanPy.Structures.Expression.Expression import Expression
from LeanPy.Structures.Expression.ExpressionManipulation import mark_as_expected_type, mark_as_external

class ValueTypeTraverser:
    def __init__(self, folder : str):
        self.folder = folder
        self.file_name_to_declaration : dict[str, Declaration] = {}
        self.active_value_type_pairs : List[Tuple[Expression, Expression]] = []

        self.type_checker = TypeChecker(fun_on_successful_equality=self.save_value_type_pair)

    def save_value_type_pair(self, value : Expression, value_type : Expression):
        value = value.source
        value_type = value_type.source
        if value.is_external and value_type.is_expected_type:
            self.active_value_type_pairs.append((value, value_type))
    
    def traverse(self, files : List[str] | None = None):
        if files is None:
            files = os.listdir(self.folder)
            # Remove the .json extension
            files = [file[:-5] for file in files if file.endswith(".json")]

        queue : List[str] = []
        def load(decl_file_name : str):
            if decl_file_name in self.file_name_to_declaration:
                return
            dependencies, declaration = LeanJSONParser.from_file(os.path.join(self.folder, f"{decl_file_name}.json"))
            self.file_name_to_declaration[decl_file_name] = declaration

            for dependency in dependencies:
                load(decl_file_name=dependency)

            self.type_checker.environment.add_declaration(declaration)
            queue.append(decl_file_name)
        
        for file in files:
            load(file)
            while len(queue) > 0:
                decl_file_name = queue.pop()
                if decl_file_name in files:
                    self.get_expected_pairs(decl_file_name)
                    print(f"start")
                    for p in self.active_value_type_pairs:
                        yield p
                    self.active_value_type_pairs.clear()
                    print(f"end")
    
    def get_expected_pairs(self, decl_file_name : str):
        declaration = self.file_name_to_declaration[decl_file_name]

        if isinstance(declaration, Definition) or isinstance(declaration, Theorem) or isinstance(declaration, Opaque):
            mark_as_external(declaration.value)
            inferred_type = self.type_checker.infer(declaration.value, True, True)
            
            mark_as_expected_type(declaration.type)
            ret = self.type_checker.def_eq(inferred_type, declaration.type, expect_true=True)
            
            assert ret

if __name__ == "__main__":
    folder = "/home/jp/projects/Mathlib4Extraction/mathlib4/json_dump"
    traverser = ValueTypeTraverser(folder)
    for value, value_type in traverser.traverse():
        print(f"Value:\n{value}\nType:\n{value_type}\n")