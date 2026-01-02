import pytest
from day_of_year import day_of_year, InvalidArgument

def test_A1():
    with pytest.raises(InvalidArgument):
        day_of_year(20)

def test_A2():
    with pytest.raises(InvalidArgument):
        day_of_year(20, 1)

def test_A3():
    with pytest.raises(InvalidArgument):
        day_of_year()

def test_A4():
    with pytest.raises(InvalidArgument):
        day_of_year(20, 13, 2020)  # Invalid month

def test_A5():
    with pytest.raises(InvalidArgument):
        day_of_year(32, 1, 2020)  # Invalid day

def test_B1():
    assert day_of_year(20, 3, 2020) == 80  # Leap year

def test_B2():
    assert day_of_year(20, 3, 2019) == 79  # Non-leap year

def test_B3():
    assert day_of_year(1, 1, 2021) == 1