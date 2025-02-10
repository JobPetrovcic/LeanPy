from typing import List, Optional

from LeanPy.Kernel.KernelErrors import LocalContextError
from LeanPy.Structures.Expression.Expression import Expression, FVar

class LocalContext:
    def __init__(self):
        self.fvars : List[FVar] = []
    
    def add_fvar(self, fvar : FVar):
        if fvar in self.fvars:
            raise LocalContextError(f"FVar {fvar} already exists in local context", fvar)
        
        self.fvars.append(fvar)    
    
    def remove_fvar(self, fvar : FVar):
        """ Removes the fvar from the local context. It must be the last fvar in the local context. """
        if len(self.fvars) == 0:
            raise LocalContextError(f"Cannot remove FVar {fvar} from empty local context", fvar)
        if not (self.fvars[-1] is fvar):
            raise LocalContextError(f"Cannot remove FVar {fvar} from local context: {self.fvars[-1]} is the last FVar", fvar)
        
        self.fvars.pop()

    def get_fvar_type(self, fvar : FVar) -> Expression:
        """ Ensures that the fvar is in the local context and returns its type. """
        if fvar in self.fvars:
            return fvar.type
        
        raise LocalContextError(f"Cannot get type: FVar {fvar.full_identifier()} not found in local context with: {[fvar.full_identifier() for fvar in self.fvars]})", fvar)
    
    def get_fvar_value(self, fvar : FVar) -> Optional[Expression]:
        """ Ensures that the fvar is in the local context and returns its value. """
        if fvar in self.fvars:
            got = fvar.val
            if got is None:
                return None
            else:
                return got
        raise LocalContextError(f"Cannot get value: FVar {fvar.full_identifier()} not found in local with: {[fvar.full_identifier() for fvar in self.fvars]})", fvar)
    
    def clear(self):
        self.fvars.clear()
    
    def is_empty(self) -> bool:
        return len(self.fvars) == 0
    
    def __str__(self) -> str:
        str_list = [fvar.full_print() for fvar in self.fvars]
        return f"LocalContext({str_list})"