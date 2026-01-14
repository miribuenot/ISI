import pytest
from transactionManager import *

def test_A1(mocker):
    tm = TransactionManager()
    transactions_ids = []
    fraud_detector = mocker.Mock()
    bank_gateway = mocker.Mock()

    with pytest.raises(ValueError):
        tm.process_batch(transactions_ids, fraud_detector, bank_gateway)
    
    assert fraud_detector.check.call_count == 0
    assert bank_gateway.transfer.call_count == 0

def test_A2(mocker):
    tm = TransactionManager()
    transactions_ids = 1
    fraud_detector = mocker.Mock()
    bank_gateway = mocker.Mock()

    with pytest.raises(ValueError):
        tm.process_batch(transactions_ids, fraud_detector, bank_gateway)
    
    assert fraud_detector.check.call_count == 0
    assert bank_gateway.transfer.call_count == 0

def test_B1(mocker):
    tm = TransactionManager()
    transactions_ids = ["TX1001"]
    fraud_detector = mocker.Mock()
    fraud_detector.check.return_value = True
    bank_gateway = mocker.Mock()

    assert tm.process_batch(transactions_ids, fraud_detector, bank_gateway) == { "success": ["TX1001"], "failed": [] }

    fraud_detector.check.assert_called_once_with("TX1001")
    bank_gateway.transfer.assert_called_once_with("TX1001")

def test_B2(mocker):
    tm = TransactionManager()
    transactions_ids = ["TX1002"]
    fraud_detector = mocker.Mock()
    fraud_detector.check.return_value = False
    bank_gateway = mocker.Mock()

    assert tm.process_batch(transactions_ids, fraud_detector, bank_gateway) == { "success": [], "failed": ["TX1002"] }

    fraud_detector.check.assert_called_once_with("TX1002")
    assert bank_gateway.transfer.call_count == 0

def test_B3(mocker):
    tm = TransactionManager()
    transactions_ids = ["TX001"]
    fraud_detector = mocker.Mock()
    fraud_detector.check.side_effect = ServiceUnavailableError()
    bank_gateway = mocker.Mock()

    with pytest.raises(ServiceUnavailableError):
        tm.process_batch(transactions_ids, fraud_detector, bank_gateway)

    fraud_detector.check.assert_called_once_with("TX001")
    assert bank_gateway.transfer.call_count == 0


def test_B4(mocker):
    tm = TransactionManager()
    transactions_ids = ["TX2001"]
    fraud_detector = mocker.Mock()
    fraud_detector.check.return_value = True
    bank_gateway = mocker.Mock()
    bank_gateway.transfer.side_effect = InsufficientFundsError()
    result = tm.process_batch(transactions_ids, fraud_detector, bank_gateway)
    
    assert result == { "success": [], "failed": ["TX2001"] }
    fraud_detector.check.assert_called_once_with("TX2001")
    bank_gateway.transfer.assert_called_once_with("TX2001")

def test_B5(mocker):
    tm = TransactionManager()
    transactions_ids = ["TX2001"]
    fraud_detector = mocker.Mock()
    fraud_detector.check.return_value = True
    bank_gateway = mocker.Mock()
    bank_gateway.transfer.side_effect = AccountFrozenError()

    with pytest.raises(AccountFrozenError):
        tm.process_batch(transactions_ids, fraud_detector, bank_gateway)

def test_C1(mocker):
    tm = TransactionManager()
    transactions_ids = ["TX1001", "TX1002"]
    fraud_detector = mocker.Mock()
    fraud_detector.check.side_effect = [True, True]
    bank_gateway = mocker.Mock()

    assert tm.process_batch(transactions_ids, fraud_detector, bank_gateway) == { "success": ["TX1001", "TX1002"], "failed": [] }

    assert fraud_detector.check.call_count == 2
    fraud_detector.check.assert_any_call("TX1002")
    fraud_detector.check.assert_any_call("TX1001")
    
    assert bank_gateway.transfer.call_count == 2
    bank_gateway.transfer.assert_any_call("TX1002")
    bank_gateway.transfer.assert_any_call("TX1001")

def test_C2(mocker):
    tm = TransactionManager()
    transactions_ids = ["TX1001", "TX1002"]
    fraud_detector = mocker.Mock()
    fraud_detector.check.side_effect = [True, False]
    bank_gateway = mocker.Mock()

    assert tm.process_batch(transactions_ids, fraud_detector, bank_gateway) == { "success": ["TX1001"], "failed": ["TX1002"] }

    assert fraud_detector.check.call_count == 2
    fraud_detector.check.assert_any_call("TX1001")
    fraud_detector.check.assert_any_call("TX1002")
    assert bank_gateway.transfer.call_count == 1
    bank_gateway.transfer.assert_called_once_with("TX1001")

def test_C3(mocker):
    tm = TransactionManager()
    transactions_ids = ["TX1001", "TX1002"]
    fraud_detector = mocker.Mock()
    fraud_detector.check.side_effect = [False, False]
    bank_gateway = mocker.Mock()

    assert tm.process_batch(transactions_ids, fraud_detector, bank_gateway) == { "success": [], "failed": ["TX1001", "TX1002"] }

    assert fraud_detector.check.call_count == 2
    assert bank_gateway.transfer.call_count == 0