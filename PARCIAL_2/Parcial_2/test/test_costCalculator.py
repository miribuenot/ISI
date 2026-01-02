import pytest
from costCalculator import CostCalculator

def test_A1(mocker):
    discountService = mocker.Mock()
    discountService.discount.return_value = 0
    additionalService = mocker.Mock()
    additionalService.cost.return_value = 60

    cc = CostCalculator(-1, "Mario", [10, 20])

    with pytest.raises(Exception):
        cc.total_cost(discountService, additionalService)
    
    # CORREGIDO: Quitados los 'assert' iniciales
    assert discountService.discount.call_count == 0
    assert additionalService.cost.call_count == 0

def test_A2(mocker):
    discountService = mocker.Mock()
    discountService.discount.return_value = 0
    additionalService = mocker.Mock()
    # Simulamos que el servicio lanza excepción si hay muchas maletas [cite: 126]
    additionalService.cost.side_effect = Exception("Too many bags")

    cc = CostCalculator(100, "Mario", [10, 20, 5, 16])

    with pytest.raises(Exception):
        cc.total_cost(discountService, additionalService)

    discountService.discount.assert_called_once_with("Mario")
    additionalService.cost.assert_called_once_with([10, 20, 5, 16])

def test_A3(mocker):
    discountService = mocker.Mock()
    discountService.discount.return_value = 0
    additionalService = mocker.Mock()
    # Simulamos excepción por peso excesivo [cite: 128]
    additionalService.cost.side_effect = Exception("Bag too heavy")

    cc = CostCalculator(100, "Mario", [10, 28])

    with pytest.raises(Exception):
        cc.total_cost(discountService, additionalService)

    discountService.discount.assert_called_once_with("Mario")
    additionalService.cost.assert_called_once_with([10, 28])

def test_B1(mocker):
    discountService = mocker.Mock()
    discountService.discount.return_value = 0
    additionalService = mocker.Mock()
    additionalService.cost.return_value = 60

    cc = CostCalculator(100, "Mario", [10, 20]) # Base 100

    assert cc.total_cost(discountService, additionalService) == 160 # 100 + 60

    discountService.discount.assert_called_once_with("Mario")
    additionalService.cost.assert_called_once_with([10, 20])

def test_B2(mocker):
    discountService = mocker.Mock()
    discountService.discount.return_value = 0
    additionalService = mocker.Mock()
    additionalService.cost.return_value = 60

    cc = CostCalculator(1000, "Mario", [10, 20]) # Base 500

    assert cc.total_cost(discountService, additionalService) == 560 # 500 + 60

    discountService.discount.assert_called_once_with("Mario")
    additionalService.cost.assert_called_once_with([10, 20])

def test_B3(mocker):
    discountService = mocker.Mock()
    discountService.discount.return_value = 0
    additionalService = mocker.Mock()
    additionalService.cost.return_value = 60

    cc = CostCalculator(3000, "Mario", [10, 20]) # Base 900

    assert cc.total_cost(discountService, additionalService) == 960 # 900 + 60

    discountService.discount.assert_called_once_with("Mario")
    additionalService.cost.assert_called_once_with([10, 20])

def test_C1(mocker):
    discountService = mocker.Mock()
    discountService.discount.return_value = 50 # 50% de descuento
    additionalService = mocker.Mock()
    additionalService.cost.return_value = 60

    cc = CostCalculator(100, "Mario", [10, 20]) # Base 100
    
    # Cálculo: (100 - 50%) + 60 = 50 + 60 = 110
    assert cc.total_cost(discountService, additionalService) == 110

    discountService.discount.assert_called_once_with("Mario")
    additionalService.cost.assert_called_once_with([10, 20])

def test_C2(mocker):
    discountService = mocker.Mock()
    discountService.discount.return_value = 50 # 50% de descuento
    additionalService = mocker.Mock()
    additionalService.cost.return_value = 60

    cc = CostCalculator(1000, "Mario", [10, 20]) # Base 500

    # CORREGIDO: Cálculo: (500 - 50%) + 60 = 250 + 60 = 310
    # Antes tenías 510 (resta directa)
    assert cc.total_cost(discountService, additionalService) == 310

    discountService.discount.assert_called_once_with("Mario")
    additionalService.cost.assert_called_once_with([10, 20])

def test_C3(mocker):
    discountService = mocker.Mock()
    discountService.discount.return_value = 50 # 50% de descuento
    additionalService = mocker.Mock()
    additionalService.cost.return_value = 60

    cc = CostCalculator(3000, "Mario", [10, 20]) # Base 900

    # CORREGIDO: Cálculo: (900 - 50%) + 60 = 450 + 60 = 510
    # Antes tenías 910
    assert cc.total_cost(discountService, additionalService) == 510

    discountService.discount.assert_called_once_with("Mario")
    additionalService.cost.assert_called_once_with([10, 20])