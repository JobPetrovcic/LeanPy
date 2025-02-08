from abc import abstractmethod


class ReducibilityHint:
    @abstractmethod
    def get_height(self) -> int:
        raise NotImplementedError("Method get_height not implemented for abstract class ReducibilityHint")

class OpaqueHint(ReducibilityHint):
    def __init__(self):
        super().__init__()
    
    def get_height(self):
        return 0
    
    def __str__(self) -> str:
        return "Opaque"

class Regular(ReducibilityHint):
    def __init__(self, depth : int):
        self.depth = depth
        super().__init__()
    
    def get_height(self):
        return self.depth
    
    def __str__(self) -> str:
        return f"Regular: {self.depth}"

class Abbrev(ReducibilityHint):
    def __init__(self):
        super().__init__()
    
    def get_height(self):
        return 0
    
    def __str__(self) -> str:
        return super().__str__()

__all__ = ['ReducibilityHint', 'OpaqueHint', 'Regular', 'Abbrev']