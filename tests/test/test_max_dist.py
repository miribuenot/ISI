import pytest
from max_dist import max_dist, InvalidArgument

def test_A1():
    with pytest.raises(InvalidArgument):
        max_dist()

def test_A2():
    with pytest.raises(InvalidArgument):
        max_dist([])

def test_B():
    with pytest.raises(TypeError):
        max_dist([1, 2, '3', 4])

def test_C1():
    assert max_dist([2,2]) == 0

def test_C2():
    assert max_dist([1,2]) == 1


def test_C3():
    assert max_dist([2,1]) == 1

def test_D1():
    assert max_dist([-1, 4, 5]) == 6

def test_D2():
    assert max_dist([5, 4, -1]) == 6

def test_D3():
    assert max_dist([-1, 5, 4]) == 6

def test_D4():
    assert max_dist([4, 5, -1]) == 6

def test_D5():
    assert max_dist([4, -1, 5]) == 6

def test_D6():
    assert max_dist([5, -1, 4]) == 6