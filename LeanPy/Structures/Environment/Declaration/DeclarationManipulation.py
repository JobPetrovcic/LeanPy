from typeguard import typechecked
from Structures.Environment.Declaration.Declaration import *

@typechecked
def is_structural_inductive(inductive : Inductive) -> bool:
    return inductive.number_of_constructors() == 1