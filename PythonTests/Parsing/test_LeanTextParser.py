from Parsing.LeanTextParser import LeanFormatParser

def test_lean_format_parser1():
    LeanFormatParser.from_file("Exports/MyNat.export")

def test_lean_format_parser2():
    LeanFormatParser.from_file("Exports/db_application.export")

def test_lean_format_parser3():
    LeanFormatParser.from_file("Exports/double.export")