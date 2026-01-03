import pytest
from doorController import DoorController, SecurityPolicyError, AccessDeniedException, AccessDeniedException, HardwareMalfunctionException, EmergencyLockdownException, NetworkException

def test_A1(mocker):

    region = "BIO-LAB-1"
    card_id = ""
    pin = "12345678"

    auth_service = mocker.Mock()
    auth_service.verify.return_value = True
    lock_mechanism = mocker.Mock()
    dc = DoorController(region)

    with pytest.raises(ValueError):
        dc.attempt_access(card_id, pin, auth_service, lock_mechanism)
    
    assert auth_service.verify.call_count == 0
    assert lock_mechanism.unlock.call_count == 0

def test_A2(mocker):

    region = "BIO-LAB-1"
    card_id = "12345678"
    pin = ""

    auth_service = mocker.Mock()
    auth_service.verify.return_value = True
    lock_mechanism = mocker.Mock()
    dc = DoorController(region)

    with pytest.raises(ValueError):
        dc.attempt_access(card_id, pin, auth_service, lock_mechanism)
    
    assert auth_service.verify.call_count == 0
    assert lock_mechanism.unlock.call_count == 0

def test_A3(mocker):

    region = "TOP-SECRET"
    card_id = "12345678"
    pin = "12345"

    auth_service = mocker.Mock()
    auth_service.verify.return_value = True
    lock_mechanism = mocker.Mock()
    dc = DoorController(region)

    with pytest.raises(SecurityPolicyError):
        dc.attempt_access(card_id, pin, auth_service, lock_mechanism)

    assert auth_service.verify.call_count == 0
    assert lock_mechanism.unlock.call_count == 0

def test_B1(mocker):
    
    region = "BIO-LAB-1"
    card_id = "12345678"
    pin = "12345678"

    auth_service = mocker.Mock()
    auth_service.verify.return_value = False
    lock_mechanism = mocker.Mock()
    dc = DoorController(region)

    with pytest.raises(AccessDeniedException):
        dc.attempt_access(card_id, pin, auth_service, lock_mechanism)

    auth_service.verify.assert_called_once_with(card_id, pin, region)
    assert lock_mechanism.unlock.call_count == 0

def test_B2(mocker):

    region = "BIO-LAB-1"
    card_id = "12345678"
    pin = "12345678"

    auth_service = mocker.Mock()
    auth_service.verify.return_value = True
    lock_mechanism = mocker.Mock()
    dc = DoorController(region)

    assert dc.attempt_access(card_id, pin, auth_service, lock_mechanism) == True

    auth_service.verify.assert_called_once_with(card_id, pin, region)
    lock_mechanism.unlock.assert_called_once()

def test_B3(mocker):

    region = "BIO-LAB-1"
    card_id = "12345678"
    pin = "12345678"

    auth_service = mocker.Mock()
    auth_service.verify.side_effect = NetworkException()
    lock_mechanism = mocker.Mock()
    dc = DoorController(region)

    with pytest.raises(NetworkException):
        dc.attempt_access(card_id, pin, auth_service, lock_mechanism)
    
    auth_service.verify.assert_called_once_with(card_id, pin, region)
    assert lock_mechanism.unlock.call_count == 0

def test_B4(mocker):
    region = "BIO-LAB-1"
    card_id = "12345678"
    pin = "12345678"

    auth_service = mocker.Mock()
    auth_service.verify.return_value = True
    lock_mechanism = mocker.Mock()
    lock_mechanism.unlock.side_effect = HardwareMalfunctionException()
    dc = DoorController(region)

    with pytest.raises(EmergencyLockdownException):
        dc.attempt_access(card_id, pin, auth_service, lock_mechanism)
    
    auth_service.verify.assert_called_once_with(card_id, pin, region)
    lock_mechanism.unlock.assert_called_once()