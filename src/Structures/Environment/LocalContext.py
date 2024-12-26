from typing import Dict, Optional

from Structures.Expression.Expression import Expression, FVar
from Structures.Expression.ExpressionManipulation import clone_expression


class LocalContext:
    def __init__(self):
        self.fvar_type : Dict[FVar, Expression] = {}
        self.fvar_value : Dict[FVar, Optional[Expression]] = {}
    
    def add_fvar(self, fvar : FVar, expr : Expression, val : Optional[Expression]):
        if fvar in self.fvar_type or fvar in self.fvar_value:
            raise ValueError(f"FVar {fvar} already exists in local context")
        self.fvar_type[fvar] = expr
        self.fvar_value[fvar] = val
    
    def remove_fvar(self, fvar : FVar):
        if fvar not in self.fvar_type or fvar not in self.fvar_value:
            raise ValueError(f"FVar {fvar} not found in local context")
        del self.fvar_type[fvar]
        del self.fvar_value[fvar]

    def get_fvar_type(self, fvar : FVar, use_same_fvars : bool) -> Expression:
        if fvar in self.fvar_type:
            return clone_expression(self.fvar_type[fvar], use_same_fvars)
        
        raise ValueError(f"FVar {fvar} with id {hex(id(fvar))} not found in local context context fvars ids: {[hex(id(fvar)) for fvar in self.fvar_type.keys()]} and names {[str(fvar) for fvar in self.fvar_type.keys()]}")
    
    def get_fvar_value(self, fvar : FVar, use_same_fvars : bool) -> Optional[Expression]:
        if fvar in self.fvar_value:
            got = self.fvar_value[fvar]
            if got is None:
                return None
            else:
                return clone_expression(got, use_same_fvars)
        raise ValueError(f"FVar {fvar} not found in local context")
    
    def clear(self):
        self.fvar_type.clear()
        self.fvar_value.clear()
    
    def is_empty(self) -> bool:
        assert len(self.fvar_type) == len(self.fvar_value), "FVar type and value dictionaries have different lengths"
        return len(self.fvar_type) == 0
    