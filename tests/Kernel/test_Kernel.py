from LeanPy.Parsing.LeanTextParser import LeanFormatParser
from LeanPy.Structures.Expression.Expression import Const

def test_decidable():
    parsed = LeanFormatParser.from_file("Exports/bool_reduction.export")
    type_checker = parsed.type_checker
    decl = type_checker.environment.get_declaration_under_name(type_checker.environment.create_name_from_str("A"))
    
    assert type_checker.def_eq(decl.value.arg, Const(type_checker.environment.Bool_true_name, []))