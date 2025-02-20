from LeanPy.Structures.Expression.Level import *


class PanicLevelError(Exception):
    def __init__(self, message : str):
        super().__init__(message)

class DefinitionalEqualityLevelError(Exception):
    def __init__(self, l : Level, r : Level):
        if isinstance(l, LevelMVar) or isinstance(r, LevelMVar):
            raise PanicLevelError("Don't use DefinitionalEqualityError with metavariables")
        
        self.l = l
        self.r = r

class UnfinishedLevelError(Exception):
    def __init__(self, source : Level):
        super().__init__("Level is unfinished, cannot continue", source)