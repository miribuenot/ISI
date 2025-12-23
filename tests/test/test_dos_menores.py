import pytest
from dos_menores import dos_menores

"Si el argumento no es una lista, devuelve None"
def test_A1():
    assert dos_menores() == None

"Si el argumento es una lista vacía, devuelve None"
def test_A2():
    assert dos_menores([]) == None

"Si la lista tiene un solo elemento, devuelve ese elemento"
def test_B1():
    assert dos_menores([5]) == 5

"Si la lista tiene dos elementos, devuelve ambos en orden"
@pytest.mark.parametrize("lista", [[3, 7], [7, 3]])
def test_C1(lista):
    assert dos_menores(lista) == (3, 7)


"Si la lista tiene varios elementos, devuelve los dos menores en orden"
@pytest.mark.parametrize("lista", [
    [5, 2, 8, 1, 4],
    [1, 2, 3, 4, 8],
    [1, 20, 5, 2],
    [1, 7, 7, 8, 7, 2],
])
def test_D1(lista):
    assert dos_menores(lista) == (1, 2)
