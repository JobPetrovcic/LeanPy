from typing import Dict, List, Tuple
from Structures.Environment.Declaration.Declaration import *
from Structures.Environment.ReducibilityHint import *
from Structures.Expression.Expression import *
from Structures.Expression.Level import *
from Structures.Name import Anonymous, Name, SubName

class ExpressionToPython:
    def __init__(self):
        self.exported : str = ""

        self.level_cnt : int = 0

        self.names : Dict[Name, str] = {} # Name -> Python name
        self.levels : Dict[Level, str] = {} # Level -> Python name
        self.expressions : Dict[Expression, str] = {} # Expression -> Python name
        self.declarations : Dict[Declaration, str] = {} # Declaration -> Python name

    def __str__(self):
        return self.exported

    def add_line(self, line : str):
        self.exported += line + "\n"
    
    def add_definition_line(self, name : str, value : str):
        self.add_line(f"{name} = {value}")

    # NAMES
    def get_name_value_str(self, name : Name) -> str:
        if isinstance(name, SubName):
            return f"SubName(anc={self.get_name(name.anc)}, name='{name.name}')"
        elif isinstance(name, Anonymous):
            return f"Anonymous()"
        else:
            raise ValueError(f"Name {name} has unknown class..")

    def add_name(self, name : Name, python_name : str | None = None):
        if python_name is None:
            python_name = f"{str(name).replace('.', '_').replace('@', 'at')}_name"
        if python_name in self.names.values():
            raise ValueError(f"Name {name} already exists in the exporter.")

        val = self.get_name_value_str(name)
        self.add_definition_line(python_name, val)
        self.names[name] = python_name

    def get_name(self, name : Name) -> str:
        if name not in self.names:
            self.add_name(name)
        return self.names[name]
    
    # LEVELS
    def get_level_value_str(self, lvl : Level, python_name : str) -> str:
        if isinstance(lvl, LevelZero):
            return "LevelZero()"
        elif isinstance(lvl, LevelSucc):
            return f"LevelSucc(anc={self.get_level(lvl.anc, python_name + '_anc')})"
        elif isinstance(lvl, LevelParam):
            return f"LevelParam(name={self.get_name(lvl.name)})"
        elif isinstance(lvl, LevelMax):
            return f"LevelMax(lhs={self.get_level(lvl.lhs, python_name + '_lhs')}, rhs={self.get_level(lvl.rhs, python_name + '_rhs')})"
        elif isinstance(lvl, LevelIMax):
            return f"LevelIMax(lhs={self.get_level(lvl.lhs, python_name + '_lhs')}, rhs={self.get_level(lvl.rhs, python_name + '_rhs')})"
        else:
            raise ValueError(f"Level {lvl} has unknown class.")

    def add_level(self, lvl : Level, python_name : str):
        if python_name in self.levels.values():
            raise ValueError(f"Level {lvl} already exists in the exporter.")

        val = self.get_level_value_str(lvl, python_name)
        self.add_definition_line(python_name, val)
        self.levels[lvl] = python_name

    def get_level(self, lvl : Level, python_name : str) -> str:
        if lvl not in self.levels:
            self.add_level(lvl, python_name)
        return self.levels[lvl]
    
    def get_level_params_str(self, lvl_params : List[LevelParam], python_name : str) -> str:
        return f"[{', '.join([self.get_level(l, python_name + '_lvlparam' + str(i)) for i, l in enumerate(lvl_params)])}]"

    def get_levels_str(self, levels : List[Level], python_name : str) -> str:
        return f"[{', '.join([self.get_level(l, python_name + '_lvl' + str(i)) for i, l in enumerate(levels)])}]"

    # EXPRESSIONS
    def get_expression_value_str(self, expr : Expression, python_name : str) -> str:
        if isinstance(expr, Sort):
            self.level_cnt += 1
            return f"Sort(level={self.get_level(expr.level, python_name + '_lvl' + str(self.level_cnt))})"
        elif isinstance(expr, Const):
            lvl_params_str = self.get_levels_str(expr.lvl_params, python_name)
            return f"Const(name={self.get_name(expr.name)}, lvl_params={lvl_params_str})"
        elif isinstance(expr, App):
            return f"App(fn={self.get_expression_value_str(expr.fn, python_name)}, arg={self.get_expression_value_str(expr.arg, python_name)})"
        elif isinstance(expr, Lambda):
            return f"Lambda(bname={self.get_name(expr.bname)}, arg_type={self.get_expression_value_str(expr.arg_type, python_name)}, body={self.get_expression_value_str(expr.body, python_name)})"
        elif isinstance(expr, Pi):
            return f"Pi(bname={self.get_name(expr.bname)}, arg_type={self.get_expression_value_str(expr.arg_type, python_name)}, body_type={self.get_expression_value_str(expr.body_type, python_name)})"
        elif isinstance(expr, Let):
            return f"Let(bname={self.get_name(expr.bname)}), arg_type={self.get_expression_value_str(expr.arg_type, python_name)}, val={self.get_expression_value_str(expr.val, python_name)}, body={self.get_expression_value_str(expr.body, python_name)}"
        elif isinstance(expr, BVar):
            return f"BVar(dbj_id={expr.dbj_id})"
        elif isinstance(expr, Proj):
            return f"Proj(type_name={self.get_name(expr.type_name)}, index={expr.index}, struct={self.get_expression_value_str(expr.struct, python_name)})"
        else:
            raise ValueError(f"Expression {expr} has unknown class : {expr.__class__}.")

    def add_expression(self, expr : Expression, python_name : str):
        if python_name in self.expressions.values():
            raise ValueError(f"Expression {expr} already exists in the exporter.")

        val = self.get_expression_value_str(expr, python_name)
        self.add_definition_line(python_name, val)
        self.expressions[expr] = python_name    
    
    def get_expression(self, expr : Expression, python_name : str) -> str:
        if expr not in self.expressions:
            self.add_expression(expr, python_name)
        return self.expressions[expr]
    
    # DECLARATION INFOS
    def get_declaration_info_value_str(self, info : DeclarationInfo) -> str:
        got_name = self.get_name(info.name)
        lvl_params_str = self.get_level_params_str(info.lvl_params, got_name)
        return f"DeclarationInfo(name={got_name}, lvl_params={lvl_params_str}, type={self.get_expression(info.type, got_name + '_info_type')})"

    # HINTS
    def get_hint_str(self, hint : ReducibilityHint) -> str:
        if isinstance(hint, OpaqueHint):
            return "OpaqueHint()"
        elif isinstance(hint, Regular):
            return f"Regular(depth={hint.depth})"
        elif isinstance(hint, Abbrev):
            return "Abbrev()"
        else:
            raise ValueError(f"Hint {hint} has unknown class.")
        
    # RECUSRION RULES
    def get_recursion_rule_value_str(self, rule : RecursionRule, python_name : str) -> str:
        return f"RecursionRule(constructor={self.get_name(rule.constructor)}, num_fields={rule.num_fields}, value={self.get_expression(rule.value, python_name + '_rec_rule')})"

    # DECLARATIONS
    def get_declaration_value_str(self, decl : Declaration, python_name : str) -> str:
        if isinstance(decl, Definition):
            return f"Definition(info={self.get_declaration_info_value_str(decl.info)}, value={self.get_expression(decl.value, python_name + '_value')}, hint= {self.get_hint_str(decl.hint)})"
        elif isinstance(decl, Theorem):
            return f"Theorem(info={self.get_declaration_info_value_str(decl.info)}, value={self.get_expression(decl.value, python_name + '_value')})"
        elif isinstance(decl, Opaque):
            return f"Opaque(info={self.get_declaration_info_value_str(decl.info)}), value={self.get_expression(decl.value, python_name + '_value')}"
        elif isinstance(decl, Axiom):
            return f"Axiom(info={self.get_declaration_info_value_str(decl.info)})"
        elif isinstance(decl, Quot):
            return f"Quot(info={self.get_declaration_info_value_str(decl.info)})"
        elif isinstance(decl, InductiveType):
            all_inductive_names_str = f"[{', '.join([self.get_name(n) for n in decl.all_inductive_names])}]"
            constructor_names_str = f"[{', '.join([self.get_name(n) for n in decl.constructor_names])}]"
            return f"InductiveType(info={self.get_declaration_info_value_str(decl.info)}, is_recursive={decl.is_recursive}, num_params={decl.num_params}, num_indices={decl.num_indices}, all_inductive_names={all_inductive_names_str}, constructor_names={constructor_names_str})"
        elif isinstance(decl, Constructor):
            return f"Constructor(info={self.get_declaration_info_value_str(decl.info)}, c_index={decl.c_index}, inductive_name={self.get_name(decl.inductive_name)}, num_params={decl.num_params}, num_fields={decl.num_fields})"
        elif isinstance(decl, Recursor):
            recursion_rules_str = f"[{', '.join([self.get_recursion_rule_value_str(r, python_name + '_rec_rule' + str(i)) for i, r in enumerate(decl.recursion_rules)])}]"
            return f"Recursor(info={self.get_declaration_info_value_str(decl.info)}, num_params={decl.num_params}, num_indices={decl.num_indices}, num_motives={decl.num_motives}, num_minors={decl.num_minors}, recursion_rules={recursion_rules_str}, isK={decl.isK})"
        else:
            raise ValueError(f"Declaration {decl} has unknown class.")
    
    def add_declaration_line(self, decl : Declaration, python_name : str):
        if python_name in self.declarations.values():
            raise ValueError(f"Declaration {decl} already exists in the exporter.")

        val = self.get_declaration_value_str(decl, python_name)
        self.add_definition_line(python_name, val)
        self.declarations[decl] = python_name

    def export_declaration(self, decl : Declaration) -> Tuple[str, str]:
        if decl not in self.declarations:
            python_name = f"decl_{str(decl.info.name).replace('.', '_').replace('@', 'at')}"
            self.add_declaration_line(decl, python_name)
        else: raise ValueError(f"Declaration {decl} already exists in the exporter.")
        return python_name, self.declarations[decl]