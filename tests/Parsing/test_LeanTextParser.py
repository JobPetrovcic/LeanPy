from typing import List, Tuple
from LeanPy.Parsing.Lean4ExportParser import Lean4ExportParser
from LeanPy.Structures.Name import *
from LeanPy.Structures.Expression.Level import *
from LeanPy.Structures.Expression.Expression import *
from LeanPy.Structures.Environment.Declarations.Declaration import *
from LeanPy.Structures.Environment.ReducibilityHint import *
from LeanPy.Structures.Expression.ExpressionToPython import ExpressionToPython


#def test_lean_format_parser1():
#    Lean4ExportParser.from_file("Exports/MyNat.export")
#
#def test_lean_format_parser2():
#    Lean4ExportParser.from_file("Exports/db_application.export")
#
#def test_lean_format_parser3():
#    Lean4ExportParser.from_file("Exports/double.export")
#
#    parsed = Lean4ExportParser.from_file("Exports/double.export")
#    environment = parsed.type_checker.environment
#
#    exporter = ExpressionToPython()
#    tests : List[Tuple[str, Declaration]] = []
#    for name, decl in environment.name_dict.items():
#        if decl is not None:
#            python_name, _ = exporter.export_declaration(decl)
#            tests.append((python_name, decl))
#
#    code = str(exporter)
#    print("""from LeanPy.Structures.Name import *
#from LeanPy.Structures.Expression.Level import *
#from LeanPy.Structures.Expression.Expression import *
#from LeanPy.Structures.Environment.Declarations.Declaration import *
#from LeanPy.Structures.Environment.ReducibilityHint import *
#""")
#    print(code)
#    exec(code, globals())
#
#    for name, decl in tests:
#        print(f"Testing {name}")
#        print(f"Lean  : {decl.info.type}")
#        print(f"Python: {globals()[name].info.type}")
#        assert str(decl.info.type) == str(globals()[name].info.type)
#        if decl.has_value():
#            print(f"Lean  : {decl.value}")
#            print(f"Python: {globals()[name].value}")
#            assert str(decl.value) == str(globals()[name].value)
#        print()