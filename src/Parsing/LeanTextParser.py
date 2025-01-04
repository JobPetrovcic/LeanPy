
from typing import Any, Iterator, List, Sequence, Tuple

from typeguard import typechecked

from Structures.Environment.Declaration.Declaration import Axiom, Constructor, Declaration, DeclarationInfo, Definition, InductiveType, Opaque, Quot, RecursionRule, Recursor, Theorem
from Structures.Environment.ReducibilityHint import Abbrev, OpaqueHint, ReducibilityHint, Regular
from Structures.Expression.Expression import *
from Structures.Expression.Level import *
from Structures.Name import *
from Kernel.TypeChecker import TypeChecker

# IMPORTANT: The input to the LeanFormatParser must be generated by the modified Lean4export tool available at https://github.com/ammkrn/lean4export @ format2024 since the official Lean4export tool does NOT export all necessary information.

class FormatError(Exception):
    def __init__(self, message: str):
        self.message = message

class LeanFormatParser:
    def __init__(self, lean_format_lines: str | Iterator[str]):
        # split lines
        self.type_checker = TypeChecker()
        
        if isinstance(lean_format_lines, str):
            lean_format_lines = iter(lean_format_lines.split("\n"))

        self.init_processing_lists()
        self.process(lean_format_lines)

    def init_processing_lists(self):
        self.hierarchical_names : List[Name] = [Anonymous()]# TODO [self.type_checker.environment.get_anonymous()]
        self.expressions : List[Expression] = []
        self.universes : List[Level] = [LevelZero()]
        self.recursor : List[RecursionRule] = [] # new in Lean 4

    @typechecked
    def process(self, lines: Iterator[str]):
        first_skipped = False
        for line in lines:
            if not first_skipped:
                first_skipped = True
                continue
            line = line.strip()
            self.process_line(line)

    @typechecked
    def assert_parts_tag(self, parts : List[str], tag : str, tag_pos : int):
        assert tag_pos >= 0, "Tag position must be non-negative"
        if len(parts) <= tag_pos:
            raise FormatError(f"Line with parts '{parts}' does not contain the tag {tag}.")
        if parts[tag_pos] != tag:
            raise FormatError(f"Line with parts '{parts}' was expected to have the tag {tag} at position {tag_pos}.")
    
    @staticmethod
    def process_types(parts: Sequence[object], expected_types : List[type]) -> List[Any]:
        if len(parts) != len(expected_types):
            raise FormatError("The number of parts and expected types must be the same")

        processed_parts : List[Any]= []
        for i, part in enumerate(parts):
            if expected_types[i] == bool:
                # ensure that it is between 0 and 1
                if not (part == "0" or part == "1"):
                    raise FormatError(f"Expected a boolean value between 0 and 1, but got {part}")
                processed_part = bool(int(str(part)))
            else:
                processed_part = expected_types[i](part)
            processed_parts.append(processed_part)
        return processed_parts
    
    def read_multiple_input(self, le : int, parts : List[str], expected_type : type) -> Tuple[List[Any], List[str]]:
        assert le>=0, "The number of elements to read must be non-negative"
        if le == 0:
            # since we are splitting " " if le = 0, we still need to remove an element from the parts
            return [], parts[1:]
        pt = LeanFormatParser.process_types(parts[:le], [expected_type] * le)
        return pt, parts[le:]
    
    def read_all(self, parts : List[str], expected_type : type) -> List[Any]:
        return LeanFormatParser.process_types(parts, [expected_type] * len(parts))

    @typechecked
    def add_content_to_hierarchical_name(self, hid : int, decl : Declaration):
        if hid == 0:
            raise FormatError("The root hierarchical name is anonymous and should not get any content")
        self.type_checker.add_declaration(self.get_hierarchical_name(hid), decl) 

    # HIERARCHICAL NAMESPACES
    @typechecked
    def add_hierarchical_name(self, hp_hid: int, hid: int, name: str):
        assert hp_hid >= 0, "Parent hierarchical id must be non-negative"
        assert hid >= 0, "Hierarchical id must be non-negative"
        
        if hp_hid >= len(self.hierarchical_names):
            raise FormatError("Parent hierarchical id must be defined before child")
        if hid != len(self.hierarchical_names):
            raise FormatError("The next hierarchical id must be the next in the List")
        if name == "":
            raise FormatError("Hierarchical name must not be empty, this is reserved for the root hierarchical name (anonymous)")
        self.hierarchical_names.append(SubName(anc=self.hierarchical_names[hp_hid], name=name))

    @typechecked
    def get_hierarchical_name(self, hid : int) -> Name:
        assert hid >= 0, "Hierarchical id must be non-negative"
        if hid >= len(self.hierarchical_names): raise FormatError("Hierarchical id must be defined before it is used")
        return self.hierarchical_names[hid]
    
    @typechecked
    def add_recursor_rule(self, rid : int, rule : RecursionRule):
        assert rid >= 0, "Recursor rule id must be non-negative"
        if rid != len(self.recursor):
            raise FormatError("The next recursor rule id must be the next in the List")
        self.recursor.append(rule)

    def get_recursor_rule(self, rid : int) -> RecursionRule:
        assert rid >= 0, "Recursor rule id must be non-negative"
        if rid >= len(self.recursor):
            raise FormatError("Recursor rule id must be defined before it is used")
        return self.recursor[rid]
    
    @typechecked
    def process_namespace_name(self, parts : List[str]):
        if parts[1] != "#NS" and parts[1] != "":
            raise FormatError("The first part of the line must be the tag or empty")

        hid, _, hp_hid, name= LeanFormatParser.process_types(parts, [int, str, int, str])
        self.add_hierarchical_name(hp_hid, hid, name)

    def process_namespace_id(self, parts : List[str]):
        self.assert_parts_tag(parts, "#NI", 1)

        hid, _, hp_hid, identifier = LeanFormatParser.process_types(parts, [int, str, int, int])
        self.add_hierarchical_name(hp_hid, hid, str(identifier))

    # LEVELS
    @typechecked
    def add_universe(self, uid : int, universe : Level):
        if uid != len(self.universes):
            raise FormatError("The next universe id must be the next in the List")
        self.universes.append(universe)
    
    @typechecked
    def get_universe(self, uid : int) -> Level:
        assert uid >= 0, "Universe id must be non-negative"
        if uid >= len(self.universes):
            raise FormatError("Universe id must be defined before it is used")
        return self.universes[uid]
    
    def get_universes(self, uids : List[int]) -> List[Level]:
        return [self.get_universe(uid) for uid in uids]
    
    def read_universes(self, parts : List[str]) -> List[Level]:
        return self.get_universes(self.read_all(parts, int))
    
    # level tags: US(successor), UM(max), UIM(impredicative max), UP(parameter)
    def add_universe_successor(self, parts : List[str]):
        self.assert_parts_tag(parts, "#US", 1)

        uid, _, up_id = LeanFormatParser.process_types(parts, [int, str, int])
        self.add_universe(uid, universe=LevelSucc(anc=self.get_universe(up_id)))

    def add_universe_max(self, parts : List[str]):
        self.assert_parts_tag(parts, "#UM", 1)

        uid, _, up_id1, up_id2 = LeanFormatParser.process_types(parts, [int, str, int, int])
        self.add_universe(uid, universe=LevelMax(lhs=self.get_universe(up_id1), rhs=self.get_universe(up_id2)))

    def add_universe_impredicative_max(self, parts : List[str]):
        self.assert_parts_tag(parts, "#UIM", 1)

        uid, _, up_id1, up_id2 = LeanFormatParser.process_types(parts, [int, str, int, int])
        self.add_universe(uid, universe=LevelIMax(lhs=self.get_universe(up_id1), rhs=self.get_universe(up_id2)))

    def add_universe_parameter(self, parts : List[str]):
        self.assert_parts_tag(parts, "#UP", 1)

        uid, _, hid = LeanFormatParser.process_types(parts, [int, str, int])
        # TODO: maybe link the level parameter to the hierarchical name?
        self.add_universe(uid, universe=LevelParam(name=self.get_hierarchical_name(hid)))

    # EXPRESSIONS
    def add_expression(self, eid : int, expression : Expression):
        assert eid >= 0, "Expression id must be non-negative"
        if eid != len(self.expressions):
            raise FormatError("The next expression id must be the next in the List")
        self.expressions.append(expression)

    def get_expression(self, eid : int) -> Expression:
        assert eid >= 0, "Expression id must be non-negative"
        if eid >= len(self.expressions):
            raise FormatError("Expression id must be defined before it is used")
        return self.expressions[eid]

    # expressions: EV(variable), ES(sort), EC(constant), EA(apply), EL(lambda), EP(pi)
    def add_expression_variable(self, parts : List[str]):
        self.assert_parts_tag(parts, "#EV", 1)

        eid, _, vid = LeanFormatParser.process_types(parts, [int, str, int])
        self.add_expression(eid, expression=BVar(dbj_id=vid))

    def add_expression_sort(self, parts : List[str]):
        self.assert_parts_tag(parts, "#ES", 1)

        eid, _, uid = LeanFormatParser.process_types(parts, [int, str, int])
        self.add_expression(eid, expression=Sort(level=self.get_universe(uid)))
    
    def add_expression_constant(self, parts : List[str]):
        self.assert_parts_tag(parts, "#EC", 1)

        expected_types = [int, str, int]
        pt = LeanFormatParser.process_types(parts[:3], expected_types)
        parts = parts[3:]
        eid, _, hid = pt
        
        # the rest are universe ids
        self.add_expression(eid, expression=Const(name=self.get_hierarchical_name(hid), lvl_params=self.read_universes(parts)))

    def add_expression_apply(self, parts : List[str]):
        self.assert_parts_tag(parts, "#EA", 1)

        eid, _, eid1, eid2 = LeanFormatParser.process_types(parts, [int, str, int, int]) # info is not used for typechecking, only for pretty printing

        self.add_expression(eid, App(fn=self.get_expression(eid1), arg=self.get_expression(eid2)))
    
    def add_expression_lambda(self, parts : List[str]):
        self.assert_parts_tag(parts, "#EL", 1)

        eid, _, _info, hid, eid1, eid2 = LeanFormatParser.process_types(parts, [int, str, str, int, int, int]) # info is not used for typechecking, only for pretty printing

        self.add_expression(eid, Lambda(bname=self.get_hierarchical_name(hid), arg_type=self.get_expression(eid1), body=self.get_expression(eid2)))

    def add_expression_let(self, parts : List[str]):
        self.assert_parts_tag(parts, "#EZ", 1)

        eid, _, hid, eid1, eid2, eid3 = LeanFormatParser.process_types(parts, [int, str, int, int, int, int])

        self.add_expression(eid, Let(bname=self.get_hierarchical_name(hid), arg_type=self.get_expression(eid1), val=self.get_expression(eid2), body=self.get_expression(eid3)))

    def add_expression_pi(self, parts : List[str]):
        self.assert_parts_tag(parts, "#EP", 1)

        eid, _, _info, hid, eid1, eid2 = LeanFormatParser.process_types(parts, [int, str, str, int, int, int]) # info is not used for typechecking, only for pretty printing

        self.add_expression(eid, Pi(bname=self.get_hierarchical_name(hid), arg_type=self.get_expression(eid1), body_type=self.get_expression(eid2)))

    def add_expression_proj(self, parts : List[str]):
        self.assert_parts_tag(parts, "#EJ", 1)

        eid, _, hid, index, struct = LeanFormatParser.process_types(parts, [int, str, int, int, int])

        self.add_expression(eid, Proj(type_name=self.get_hierarchical_name(hid), index=index, struct=self.get_expression(struct)))

    def add_expression_nat_lit(self, parts : List[str]):
        self.assert_parts_tag(parts, "#ELN", 1)

        eid, _, val = LeanFormatParser.process_types(parts, [int, str, int])

        self.add_expression(eid, NatLit(val))
    
    def add_expression_string_lit(self, parts : List[str]):
        self.assert_parts_tag(parts, "#ELS", 1)

        eid, _ = LeanFormatParser.process_types(parts[:2], [int, str])
        parts = parts[2:]
        # the rest are hexadecimal values of utf-8 characters
        
        types = [str] * len(parts)
        pt : List[str] = LeanFormatParser.process_types(parts, types)
        s = hex_list_to_string(str_list_to_hex_list(pt))
        self.add_expression(eid, StringLit(s))
    
    def get_lvl_params(self, hids : List[int]) -> List[LevelParam]:
        return [LevelParam(name=self.get_hierarchical_name(hid)) for hid in hids]
    
    def read_lvl_params(self, parts : List[str]) -> List[LevelParam]:
        return self.get_lvl_params(self.read_all(parts, int))

    # SPECIAL
    # special: DEF(definition), AX(axiom), IND(inductive), QUOT(quotient type)
    # note: for special the tag is now the 0-th (first) part
    def add_definition(self, parts : List[str]):
        self.assert_parts_tag(parts, "#DEF", 0)
        # "#DEF {← dumpName c} {← dumpExpr val.type} {← dumpExpr val.value} {dumpHints val.hints} {← seq <$> val.levelParams.mapM dumpName}"
        types = [str, int, int, int, str]
        _, hid, val_type, val_eid, hint = LeanFormatParser.process_types(parts[:5], types)
        parts = parts[5:]
        
        rhint : ReducibilityHint
        if hint == "O":
            rhint = OpaqueHint()
        elif hint == "R":
            n = LeanFormatParser.process_types(parts[:1], [int])[0]
            rhint = Regular(n)
            parts = parts[1:]
        elif hint == "A":
            rhint = Abbrev()
        else:
            raise ValueError(f"Unknown hint {hint}")

        lvl_params : List[LevelParam] = self.read_lvl_params(parts)

        decl_info = DeclarationInfo(name=self.get_hierarchical_name(hid), lvl_params=lvl_params, type=self.get_expression(val_type))

        self.add_content_to_hierarchical_name(
            hid,
            Definition(info=decl_info, value=self.get_expression(val_eid), hint=rhint)
        )

    def add_theorem(self, parts : List[str]):
        # "#THM {← dumpName c} {← dumpExpr val.type} {← dumpExpr val.value} {← seq <$> val.levelParams.mapM dumpName}"
        self.assert_parts_tag(parts, "#THM", 0)
        
        types = [str, int, int, int]
        _, hid, val_type, val_eid = LeanFormatParser.process_types(parts[:4], types)
        parts = parts[4:]

        lvl_params : List[LevelParam] = self.read_lvl_params(parts)

        decl_info = DeclarationInfo(name=self.get_hierarchical_name(hid), lvl_params=lvl_params, type=self.get_expression(val_type))

        self.add_content_to_hierarchical_name(
            hid,
            Theorem(info=decl_info, value=self.get_expression(val_eid))
        )
        
    def add_opaque(self, parts : List[str]):
        # "#OPAQ {← dumpName c} {← dumpExpr val.type} {← dumpExpr val.value} {← seq <$> val.levelParams.mapM dumpName}"
        self.assert_parts_tag(parts, "#OPAQ", 0)
        types = [str, int, int, int]
        _, hid, val_type, val_eid = LeanFormatParser.process_types(parts[:4], types)
        parts = parts[4:]

        lvl_params : List[LevelParam] = self.read_lvl_params(parts)

        decl_info = DeclarationInfo(name=self.get_hierarchical_name(hid), lvl_params=lvl_params, type=self.get_expression(val_type))

        self.add_content_to_hierarchical_name(
            hid,
            Opaque(info=decl_info, value=self.get_expression(val_eid))
        )

    def add_axiomatic_definition(self, parts : List[str]):
        # "#AX {← dumpName c} {← dumpExpr val.type} {← seq <$> val.levelParams.mapM dumpName}"
        self.assert_parts_tag(parts, "#AX", 0)

        types = [str, int, int]
        _, hid, val_type = LeanFormatParser.process_types(parts[:3], types)
        parts = parts[3:]

        lvl_params : List[LevelParam] = self.read_lvl_params(parts)

        decl_info = DeclarationInfo(name=self.get_hierarchical_name(hid), lvl_params=lvl_params, type=self.get_expression(val_type))

        self.add_content_to_hierarchical_name(hid, Axiom(info=decl_info))

    def add_inductive_definition(self, parts : List[str]):
        # lean4export does not correctly export everything. A modification MUST be used: https://github.com/ammkrn/lean4export
        # the modification exports this as follows:
        # "#IND {← dumpName c} {← dumpExpr val.type} {isRec} {isNested} {val.numParams} {val.numIndices} {indNameIdxs.length} {seq indNameIdxs} {val.numCtors} {seq ctorNameIdxs} {← seq <$> val.levelParams.mapM dumpName}"

        self.assert_parts_tag(parts, "#IND", 0)
        # the types of only the first 8 parts
        types =[str, int, int, bool, bool, int, int, int]
        _, hid, val_eid, is_rec, _is_nested, num_params, num_indices, num_ind_name_idxs = LeanFormatParser.process_types(parts[0:8], types)
        # TODO: what is is_nested?

        parts = parts[8:]

        # then follow indNames
        ind_name_types = [int] * num_ind_name_idxs
        ind_name_pt = LeanFormatParser.process_types(parts[0 : num_ind_name_idxs], ind_name_types)
        ind_name_pt, parts = self.read_multiple_input(num_ind_name_idxs, parts, int)

        ind_names : List[Name] = []
        for ind_name in ind_name_pt:
            ind_names.append(self.get_hierarchical_name(ind_name))

        
        # then follows the number of constructors
        ctor_num_type = [int]
        num_ctor_pt = LeanFormatParser.process_types(parts[0:1], ctor_num_type)
        num_constructors = num_ctor_pt[0]

        parts = parts[1:]

        # then follow the constructor names
        ctor_name_pt, parts = self.read_multiple_input(num_constructors, parts, int)

        constructor_names : List[Name] = []
        for ctor_name in ctor_name_pt:
            constructor_names.append(self.get_hierarchical_name(ctor_name))

        # the rest are hierarchical ids for the level params
        # THE NUMBER OF LEVEL PARAMETERS IS NOT THE SAME AS THE NUMBER OF PARAMETERS
        lvl_params : List[LevelParam] = self.read_lvl_params(parts)
        
        decl_info = DeclarationInfo(name=self.get_hierarchical_name(hid), lvl_params=lvl_params, type=self.get_expression(val_eid))

        self.add_content_to_hierarchical_name(hid, 
            InductiveType(
                info=decl_info,
                is_recursive=is_rec,
                num_params=num_params,
                num_indices=num_indices,
                all_inductive_names=ind_names,
                constructor_names=constructor_names
            )
        )

    def add_quotient_definition(self, parts : List[str]) -> None:
        # "#QUOT {← dumpName c} {← dumpExpr val.type} {← seq <$> val.levelParams.mapM dumpName}"
        types = [str, int, int]
        _, hid, val_eid = LeanFormatParser.process_types(parts[:3], types)
        parts = parts[3:]
        lvl_params = self.read_lvl_params(parts)
        decl_info = DeclarationInfo(name=self.get_hierarchical_name(hid), lvl_params=lvl_params, type=self.get_expression(val_eid))

        self.add_content_to_hierarchical_name(hid, Quot(info=decl_info))

    def add_constructor_definition(self, parts : List[str]):
        # "#CTOR {← dumpName c} {← dumpExpr val.type} {← dumpName val.induct} {val.cidx} {val.numParams} {val.numFields} {← seq <$> val.levelParams.mapM dumpName}"
        types = [str, int, int, int, int, int, int]

        # NUM OF PARAMETERS IS NOT THE SAME AS NUMBER OF LEVEL PARAMETERS
        _, hid, val_eid, induct_hid, cidx, num_params, num_fields = LeanFormatParser.process_types(parts[:7], types)
        parts = parts[7:]
        # TODO: what is cidx?

        # the rest are hierarchical ids for the level params
        lvl_params = self.get_lvl_params(LeanFormatParser.process_types(parts, [int] * len(parts)))

        decl_info = DeclarationInfo(name=self.get_hierarchical_name(hid), lvl_params=lvl_params, type=self.get_expression(val_eid))

        self.add_content_to_hierarchical_name(hid,
            Constructor(
                info=decl_info,
                c_index=cidx,
                inductive_name=self.get_hierarchical_name(induct_hid),
                num_params=num_params,
                num_fields=num_fields,
            )
        )

    def add_recursor_rule_definition(self, parts : List[str]):
        # rid #RR {← dumpName rule.ctor} {rule.nfields} {← dumpExpr rule.rhs}
        self.assert_parts_tag(parts, "#RR", 1)
        rid, _, hid, num_fields, rhs_eid = LeanFormatParser.process_types(parts, [int, str, int, int, int])

        self.add_recursor_rule(
            rid, 
            RecursionRule(
                constructor=self.get_hierarchical_name(hid),
                num_fields=num_fields,
                value=self.get_expression(rhs_eid)
            )
        )

    def add_recursor_definition(self, parts : List[str]):
        # "#REC {← dumpName c} {← dumpExpr val.type} {indNameIdxs.length} {seq indNameIdxs} {val.numParams} {val.numIndices} {val.numMotives} {val.numMinors} {ruleIdxs.length} {seq ruleIdxs} {k} {← seq <$> val.levelParams.mapM dumpName}"

        self.assert_parts_tag(parts, "#REC", 0)
        types = [str, int, int, int]
        _, hid, val_type, num_ind_name_idxs = LeanFormatParser.process_types(parts[:4], types)
        parts = parts[4:]

        ind_name_pt, parts = self.read_multiple_input(num_ind_name_idxs, parts, int)
        ind_names : List[Name] = []
        for ind_name in ind_name_pt:
            ind_names.append(self.get_hierarchical_name(ind_name))

        num_params, num_indices, num_motives, num_minors, num_rule_idxs = LeanFormatParser.process_types(parts[:5], [int] * 5)
        parts = parts[5:]

        rule_idxs, parts = self.read_multiple_input(num_rule_idxs, parts, int)
        
        isK = LeanFormatParser.process_types(parts[:1], [bool])[0]
        parts = parts[1:]

        # the rest are hierarchical ids for the level params
        lvl_params = self.read_lvl_params(parts)

        decl_info = DeclarationInfo(name=self.get_hierarchical_name(hid), lvl_params=lvl_params, type=self.get_expression(val_type))

        self.add_content_to_hierarchical_name(
            hid,
            Recursor(
                info=decl_info,
                num_params=num_params,
                num_indices=num_indices,
                num_motives=num_motives,
                num_minors=num_minors,
                recursion_rules=[self.get_recursor_rule(rid) for rid in rule_idxs],
                isK=isK
            )
        )

    def process_line(self, line : str):
        print(line)
        # split the line into parts separated by exactly one space
        parts = line.split(" ")

        # HIERARCHICAL NAMESPACES
        if parts[1] == "#NS" or parts[1] == "": self.process_namespace_name(parts)
        elif parts[1] == "#NI": self.process_namespace_id(parts)

        # LEVELS
        elif parts[1] == "#US": self.add_universe_successor(parts)
        elif parts[1] == "#UM": self.add_universe_max(parts)
        elif parts[1] == "#UIM": self.add_universe_impredicative_max(parts)
        elif parts[1] == "#UP": self.add_universe_parameter(parts)

        # EXPRESSIONS
        elif parts[1] == "#EV": self.add_expression_variable(parts)
        elif parts[1] == "#ES": self.add_expression_sort(parts)
        elif parts[1] == "#EC": self.add_expression_constant(parts)
        elif parts[1] == "#EA": self.add_expression_apply(parts)
        elif parts[1] == "#EP": self.add_expression_pi(parts)
        elif parts[1] == "#EL": self.add_expression_lambda(parts)
        elif parts[1] == "#EZ" : self.add_expression_let(parts)
        elif parts[1] == "#EJ" : self.add_expression_proj(parts)
        elif parts[1] == "#ELN": self.add_expression_nat_lit(parts)
        elif parts[1] == "#ELS": self.add_expression_string_lit(parts)

        # SPECIAL
        elif parts[1] == "#RR": self.add_recursor_rule_definition(parts)

        elif parts[0] == "#DEF": self.add_definition(parts)
        elif parts[0] == "#THM": self.add_theorem(parts)
        elif parts[0] == "#OPAQ": self.add_opaque(parts)
        elif parts[0] == "#AX": self.add_axiomatic_definition(parts)
        elif parts[0] == "#IND": self.add_inductive_definition(parts)
        elif parts[0] == "#REC": self.add_recursor_definition(parts)
        elif parts[0] == "#CTOR": self.add_constructor_definition(parts)
        elif parts[0] == "#QUOT": self.add_quotient_definition(parts)
        elif parts[0] == "#PREFIX":
            # TODO: check that this is probably not needed
            raise NotImplementedError("Prefix types are not supported")
        else: raise ValueError(f"None of the tags {parts[0]} and {parts[1]} are known")

    @staticmethod
    def from_file(file_path : str):
        with open(file_path, "r") as file:
            return LeanFormatParser(file)

def hex_list_to_string(hex_list : List[int]) -> str:
    """Converts a list of integers representing a hexadecimal-encoded UTF-8 string to a string."""
    # Convert the list of integers to a bytes object
    byte_array = bytes(hex_list)
    
    # Decode the bytes object using UTF-8
    return byte_array.decode('utf-8')

def str_list_to_hex_list(str_list : List[str]) -> List[int]:
    """
    Converts a list of strings, representing the hexadecimal values of a UTF-8 encoded string, to a list of integers.
    Example:
        ["61", "62", "63"] -> [97, 98, 99]
    """
    return [int(s, 16) for s in str_list]