class ReducibilityHint:
    pass

class OpaqueHint(ReducibilityHint):
    def __init__(self):
        super().__init__()

class Regular(ReducibilityHint):
    def __init__(self, depth : int):
        self.depth = depth
        super().__init__()

class Abbrev(ReducibilityHint):
    def __init__(self):
        super().__init__()