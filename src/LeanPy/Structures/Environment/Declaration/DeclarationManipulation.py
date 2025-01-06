from typeguard import typechecked
from LeanPy.Structures.Environment.Declaration.Declaration import *

@typechecked
def is_structural_inductive(inductive : InductiveType) -> bool:
    return inductive.number_of_constructors() == 1