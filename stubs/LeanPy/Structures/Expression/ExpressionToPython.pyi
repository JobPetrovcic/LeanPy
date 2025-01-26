from Structures.Environment.Declaration.Declaration import *
from Structures.Environment.ReducibilityHint import *
from Structures.Expression.Expression import *
from Structures.Expression.Level import *
from Structures.Name import Name as Name
from _typeshed import Incomplete

class ExpressionToPython:
    exported: str
    level_cnt: int
    names: Incomplete
    levels: Incomplete
    expressions: Incomplete
    declarations: Incomplete
    def __init__(self) -> None: ...
    def add_line(self, line: str): ...
    def add_definition_line(self, name: str, value: str): ...
    def get_name_value_str(self, name: Name) -> str: ...
    def add_name(self, name: Name, python_name: str | None = None): ...
    def get_name(self, name: Name) -> str: ...
    def get_level_value_str(self, lvl: Level, python_name: str) -> str: ...
    def add_level(self, lvl: Level, python_name: str): ...
    def get_level(self, lvl: Level, python_name: str) -> str: ...
    def get_level_params_str(self, lvl_params: list[LevelParam], python_name: str) -> str: ...
    def get_levels_str(self, levels: list[Level], python_name: str) -> str: ...
    def get_expression_value_str(self, expr: Expression, python_name: str) -> str: ...
    def add_expression(self, expr: Expression, python_name: str): ...
    def get_expression(self, expr: Expression, python_name: str) -> str: ...
    def get_declaration_info_value_str(self, info: DeclarationInfo) -> str: ...
    def get_hint_str(self, hint: ReducibilityHint) -> str: ...
    def get_recursion_rule_value_str(self, rule: RecursorRule, python_name: str) -> str: ...
    def get_declaration_value_str(self, decl: Declaration, python_name: str) -> str: ...
    def add_declaration_line(self, decl: Declaration, python_name: str): ...
    def export_declaration(self, decl: Declaration) -> tuple[str, str]: ...
