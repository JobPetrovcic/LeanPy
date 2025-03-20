from LeanPy.Structures.Expression.LevelManipulation import is_equivalent
from LeanPy.Structures.Expression.LevelErrors import DefinitionalEqualityLevelError
from LeanPy.Structures.Name import *
from LeanPy.Structures.Expression.Level import *
import pytest

from LeanPy.Structures.Name import string_to_name

def test_is_equivalent_definitional_error1():
    l = LevelZero()
    r = LevelSucc(l)
    # Since LevelZero and LevelSucc(LevelZero) are not structurally equal,
    # is_equivalent should raise DefinitionalEqualityLevelError when expect_true is True.
    with pytest.raises(DefinitionalEqualityLevelError):
        is_equivalent(l, r, True)

def test_is_equivalent_definitional_error2():
    l = LevelZero()
    r = LevelMax(LevelParam(string_to_name("l")), LevelParam(string_to_name("r")))
    # Since LevelZero and LevelSucc(LevelZero) are not structurally equal,
    # is_equivalent should raise DefinitionalEqualityLevelError when expect_true is True.
    with pytest.raises(DefinitionalEqualityLevelError):
        is_equivalent(l, r, True)

def test_is_equivalent_definitional_error3():
    l = LevelZero()
    r = LevelIMax(LevelParam(string_to_name("l")), LevelParam(string_to_name("r")))
    # Since LevelZero and LevelSucc(LevelZero) are not structurally equal,
    # is_equivalent should raise DefinitionalEqualityLevelError when expect_true is True.
    with pytest.raises(DefinitionalEqualityLevelError):
        is_equivalent(l, r, True)