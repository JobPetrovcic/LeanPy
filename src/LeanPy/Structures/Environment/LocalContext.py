from typing import Set, Optional

from typeguard import typechecked

from LeanPy.Structures.Expression.Expression import Expression, FVar

class LocalContext:
    def __init__(self):
        self.fvars : Set[FVar] = set()
    
    @typechecked
    def add_fvar(self, fvar : FVar):
        if fvar in self.fvars:
            raise ValueError(f"FVar {fvar} already exists in local context")
        
        self.fvars.add(fvar)    
    
    @typechecked
    def remove_fvar(self, fvar : FVar):
        if fvar not in self.fvars:
            raise ValueError(f"FVar {fvar} not found in local context")
        
        self.fvars.remove(fvar)

    @typechecked
    def get_fvar_type(self, fvar : FVar) -> Expression:
        if fvar in self.fvars:
            return fvar.type
        
        raise ValueError(f"Cannot get type: FVar {fvar.full_identifier()} not found in local context with: {[fvar.full_identifier() for fvar in self.fvars]})")
    
    @typechecked
    def get_fvar_value(self, fvar : FVar) -> Optional[Expression]:
        if fvar in self.fvars:
            got = fvar.val
            if got is None:
                return None
            else:
                return got
        raise ValueError(f"Cannot get value: FVar {fvar.full_identifier()} not found in local with: {[fvar.full_identifier() for fvar in self.fvars]})")
    
    def clear(self):
        print(f"Context cleared")
        self.fvars.clear()
    
    def is_empty(self) -> bool:
        return len(self.fvars) == 0
    
    def __str__(self) -> str:
        str_list = [fvar.full_print() for fvar in self.fvars]
        return f"LocalContext({str_list})"