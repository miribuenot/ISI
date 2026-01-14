import pytest
from healthMonitor import *

def test_A1(mocker):
    patient_id = "001"
    sensor_suite = mocker.Mock()
    sensor_suite.get_battery_level.return_value = 10
    sensor_suite.read_heart_rate.return_value = 75
    notifier = mocker.Mock()

    monitor = HealthMonitor()
    
    assert monitor.check_patient_status(patient_id, sensor_suite, notifier) == "STABLE"

    assert sensor_suite.get_battery_level.call_count == 1
    assert sensor_suite.read_heart_rate.call_count == 1
    assert sensor_suite.read_oxygen_saturation.call_count == 0
    assert notifier.alert_doctor.call_count == 0
    assert notifier.alert_nurse.call_count == 0

def test_A2(mocker):
    patient_id = "001"
    sensor_suite = mocker.Mock()
    sensor_suite.get_battery_level.return_value = 50
    sensor_suite.read_heart_rate.return_value = 75
    sensor_suite.read_oxygen_saturation.return_value = 99
    notifier = mocker.Mock()

    monitor = HealthMonitor()

    assert monitor.check_patient_status(patient_id, sensor_suite, notifier) == "STABLE"

    assert sensor_suite.get_battery_level.call_count == 1
    assert sensor_suite.read_heart_rate.call_count == 1
    assert sensor_suite.read_oxygen_saturation.call_count == 1
    assert notifier.alert_doctor.call_count == 0
    assert notifier.alert_nurse.call_count == 0

def test_A3_low_battery_critical(mocker):

    patient_id = "001"
    sensor_suite = mocker.Mock()
    sensor_suite.get_battery_level.return_value = 15  
    sensor_suite.read_heart_rate.return_value = 150  
    notifier = mocker.Mock()

    monitor = HealthMonitor()


    result = monitor.check_patient_status(patient_id, sensor_suite, notifier)

    assert result == "CRITICAL"

    notifier.alert_doctor.assert_called_once_with(patient_id, "HR_CRITICAL")
    

    assert sensor_suite.read_oxygen_saturation.call_count == 0

def test_A4(mocker):
    patient_id = "001"
    sensor_suite = mocker.Mock()
    sensor_suite.get_battery_level.return_value = 10
    sensor_suite.read_heart_rate.side_effect = SensorReadError()
    sensor_suite.read_oxygen_saturation.return_value = 85
    notifier = mocker.Mock()

    monitor = HealthMonitor()

    with pytest.raises(CriticalMonitorFailure):
        monitor.check_patient_status(patient_id, sensor_suite, notifier)

    assert sensor_suite.get_battery_level.call_count == 1
    assert sensor_suite.read_heart_rate.call_count == 1
    assert sensor_suite.read_oxygen_saturation.call_count == 0
    assert notifier.alert_doctor.call_count == 0
    assert notifier.alert_nurse.call_count == 0

def test_B1(mocker):
    patient_id = "001"
    sensor_suite = mocker.Mock()
    sensor_suite.get_battery_level.return_value = 50
    sensor_suite.read_heart_rate.return_value = 20
    notifier = mocker.Mock()

    monitor = HealthMonitor()

    assert monitor.check_patient_status(patient_id, sensor_suite, notifier) == "CRITICAL"

    assert sensor_suite.get_battery_level.call_count == 1
    assert sensor_suite.read_heart_rate.call_count == 1
    assert sensor_suite.read_oxygen_saturation.call_count == 0
    notifier.alert_doctor.assert_called_once_with(patient_id, "HR_CRITICAL")
    assert notifier.alert_nurse.call_count == 0

def test_B2(mocker):
    patient_id = "001"
    sensor_suite = mocker.Mock()
    sensor_suite.get_battery_level.return_value = 50
    sensor_suite.read_heart_rate.return_value = 200
    notifier = mocker.Mock()

    monitor = HealthMonitor()

    assert monitor.check_patient_status(patient_id, sensor_suite, notifier) == "CRITICAL"

    assert sensor_suite.get_battery_level.call_count == 1
    assert sensor_suite.read_heart_rate.call_count == 1
    assert sensor_suite.read_oxygen_saturation.call_count == 0
    notifier.alert_doctor.assert_called_once_with(patient_id, "HR_CRITICAL")
    assert notifier.alert_nurse.call_count == 0

def test_B3(mocker):
    patient_id = "001"
    sensor_suite = mocker.Mock()
    sensor_suite.get_battery_level.return_value = 50
    sensor_suite.read_heart_rate.side_effect = SensorReadError()
    sensor_suite.read_oxygen_saturation.return_value = 85
    notifier = mocker.Mock()

    monitor = HealthMonitor()

    with pytest.raises(CriticalMonitorFailure):
        monitor.check_patient_status(patient_id, sensor_suite, notifier)

    assert sensor_suite.get_battery_level.call_count == 1
    assert sensor_suite.read_heart_rate.call_count == 1
    assert sensor_suite.read_oxygen_saturation.call_count == 0
    assert notifier.alert_doctor.call_count == 0
    assert notifier.alert_nurse.call_count == 0

def test_C1(mocker):
    patient_id = "001"
    sensor_suite = mocker.Mock()
    sensor_suite.get_battery_level.return_value = 50
    sensor_suite.read_heart_rate.return_value = 75
    sensor_suite.read_oxygen_saturation.return_value = 85
    notifier = mocker.Mock()

    monitor = HealthMonitor()

    assert monitor.check_patient_status(patient_id, sensor_suite, notifier) == "WARNING"

    assert sensor_suite.get_battery_level.call_count == 1
    assert sensor_suite.read_heart_rate.call_count == 1
    assert sensor_suite.read_oxygen_saturation.call_count == 1
    assert notifier.alert_doctor.call_count == 0
    notifier.alert_nurse.assert_called_once_with(patient_id, "O2_LOW")

def test_C2(mocker):
    patient_id = "001"
    sensor_suite = mocker.Mock()
    sensor_suite.get_battery_level.return_value = 50
    sensor_suite.read_heart_rate.return_value = 110
    sensor_suite.read_oxygen_saturation.side_effect = SensorReadError()
    notifier = mocker.Mock()

    monitor = HealthMonitor()

    assert monitor.check_patient_status(patient_id, sensor_suite, notifier) == "STABLE"

    assert sensor_suite.get_battery_level.call_count == 1
    assert sensor_suite.read_heart_rate.call_count == 1
    assert sensor_suite.read_oxygen_saturation.call_count == 1
    assert notifier.alert_doctor.call_count == 0
    assert notifier.alert_nurse.call_count == 0