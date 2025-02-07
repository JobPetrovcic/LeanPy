from LeanPy.Parsing.Lean4ExportParser import Lean4ExportParser
from LeanPy.Structures.Expression.Expression import Const

def test_decidable():
    parsed = Lean4ExportParser.from_file("Exports/bool_reduction.export")
    type_checker = parsed.type_checker
    decl = type_checker.environment.get_declaration_under_name(string_to_name("A"))
    
    assert type_checker.def_eq(decl.value.arg, Const(type_checker.environment.Bool_true_name, []))