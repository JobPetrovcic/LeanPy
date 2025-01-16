from Parsing.LeanTextParser import LeanFormatParser
from Structures.Name import *
from Structures.Expression.Level import *
from Structures.Expression.Expression import *
from Structures.Environment.Declaration.Declaration import *
from Structures.Environment.ReducibilityHint import *
from Structures.Expression.ExpressionToPython import ExpressionToPython

# run: python3 create_initial_definitions.py > Structures/Environment/initial_definitions.py

if __name__=='__main__':
    parsed = LeanFormatParser.from_file("../Exports/double.export")
    environment = parsed.type_checker.environment

    exporter = ExpressionToPython()
    for name, decl in environment.name_dict.items():
        if decl is not None:
            python_name, decl_str = exporter.export_declaration(decl)
            exporter.add_line(f"env.add_declaration({exporter.get_name(decl.info.name)}, {python_name})\n")

    code = str(exporter)
    initial_definitions_str = """from Structures.Name import *
from Structures.Expression.Level import *
from Structures.Expression.Expression import *
from Structures.Environment.Declaration.Declaration import *
from Structures.Environment.ReducibilityHint import *
          
from Structures.Environment.Environment import Environment
          

def init_basic_definitions(env : Environment):
"""
    initial_definitions_str += "\t"+"\n\t".join(code.splitlines())
    print(initial_definitions_str)