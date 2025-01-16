from Parsing.LeanTextParser import LeanFormatParser
from Structures.Expression.Expression import App, Const

if __name__ == "__main__":
    
    #LeanFormatParser.from_file("../Exports/gt.export")
    #LeanFormatParser.from_file("../Exports/quot.export")
    #LeanFormatParser.from_file("../Exports/double_let.export")
    LeanFormatParser.from_file("../Exports/add_const_map.export")
    #parsed = LeanFormatParser.from_file("../Exports/bool_reduction.export")
    #type_checker = parsed.type_checker
    #decl = type_checker.environment.get_declaration_under_name(type_checker.environment.create_name_from_str("A"))
    #
    #assert type_checker.def_eq(decl.value.arg, Const(type_checker.environment.Bool_true_name, []))

    #parsed = LeanFormatParser.from_file("../Exports/beq.export")
    #tc = parsed.type_checker

    #nct = tc.environment.get_declaration_under_name(tc.environment.create_name_from_str("Bool.noConfusionType"))
    #
    #true = Const(tc.environment.Bool_true_name, [])
    #false = Const(tc.environment.Bool_false_name, [])

    #test1 = App(Const(nct.info.name, nct.info.lvl_params), false)
    #test2 = App(test1, true)
    #test3 = App(test2, false)
    #print(tc.def_eq_core(false, test3))
    #print(tc.whnf(test3))
    #print(tc.environment.create_name_from_str("Bool.noConfusionType") == tc.environment.create_name_from_str("Bool.noConfusionType"))

    #zero = Const(tc.environment.Nat_zero_name, [])
    #beq = Const(tc.environment.Nat_beq_name, [])
    #test = App(App(beq, zero), zero)
    #print(tc.whnf(test))

    #LeanFormatParser.from_file("../Exports/myfunext.export")
    #LeanFormatParser.from_file("../Exports/myfunext_1let.export")
    #LeanFormatParser.from_file("../Exports/myfunext_2let.export")
    #LeanFormatParser.from_file("../Exports/funext.export")
    #LeanFormatParser.from_file("../Exports/axiomK.export")
    #LeanFormatParser.from_file("../Exports/unit_eq.export")
    #LeanFormatParser.from_file("../Exports/let_thm.export")
    #LeanFormatParser.from_file("../Exports/let_thm2.export")
    #LeanFormatParser.from_file("../Exports/let.export")
    #LeanFormatParser.from_file("../Exports/eta.export")
    #LeanFormatParser.from_file("../Exports/struct.export")
