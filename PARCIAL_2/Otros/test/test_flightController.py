import pytest
from flightController import *

def test_A(mocker):
    max_wind_speed_allowed = 15  # Example maximum wind speed allowed for takeoff
    fc = FlightController(max_wind_speed_allowed)
    drone_id = "AA1234"
    battery_percent = 5
    flight_type = "COMMERCIAL"
    WeatherService = mocker.Mock()
    WeatherService.get_current_wind_speed.return_value = 10
    RadioSystem = mocker.Mock()
    RadioSystem.send_clearance.return_value = True

    with pytest.raises(LowBatteryError):
        fc.authorize_takeoff(drone_id, battery_percent, flight_type, WeatherService, RadioSystem)
    
    assert WeatherService.get_current_wind_speed.call_count == 0
    assert RadioSystem.send_clearance.call_count == 0

def test_B1(mocker):
    max_wind_speed_allowed = 15
    fc = FlightController(max_wind_speed_allowed)
    drone_id = "AA1234"
    battery_percent = 50
    flight_type = "COMMERCIAL"
    WeatherService = mocker.Mock()
    WeatherService.get_current_wind_speed.return_value = 25
    RadioSystem = mocker.Mock()
    RadioSystem.send_clearance.return_value = True

    with pytest.raises(UnsafeWeatherError):
        fc.authorize_takeoff(drone_id, battery_percent, flight_type, WeatherService, RadioSystem)

    WeatherService.get_current_wind_speed.assert_called_once()
    assert RadioSystem.send_clearance.call_count == 0

def test_B2(mocker):
    max_wind_speed_allowed = 15
    fc = FlightController(max_wind_speed_allowed)
    drone_id = "AA1234"
    battery_percent = 50
    flight_type = "EMERGENCY"
    WeatherService = mocker.Mock()
    WeatherService.get_current_wind_speed.return_value = 20
    RadioSystem = mocker.Mock()
    RadioSystem.send_clearance.return_value = True

    clearance = fc.authorize_takeoff(drone_id, battery_percent, flight_type, WeatherService, RadioSystem)

    WeatherService.get_current_wind_speed.assert_called_once()
    RadioSystem.send_clearance.assert_called_once_with(drone_id)
    assert clearance == True

def test_B3(mocker):
    max_wind_speed_allowed = 15
    fc = FlightController(max_wind_speed_allowed)
    drone_id = "AA1234"
    battery_percent = 50
    flight_type = "EMERGENCY"
    WeatherService = mocker.Mock()
    WeatherService.get_current_wind_speed.return_value = 35
    RadioSystem = mocker.Mock()
    RadioSystem.send_clearance.return_value = True

    with pytest.raises(UnsafeWeatherError):
        fc.authorize_takeoff(drone_id, battery_percent, flight_type, WeatherService, RadioSystem)

    WeatherService.get_current_wind_speed.assert_called_once()
    assert RadioSystem.send_clearance.call_count == 0

def test_B4(mocker):
    max_wind_speed_allowed = 15
    fc = FlightController(max_wind_speed_allowed)
    drone_id = "AA1234"
    battery_percent = 50
    flight_type = "COMMERCIAL"
    WeatherService = mocker.Mock()
    WeatherService.get_current_wind_speed.side_effect = SensorOfflineException()
    RadioSystem = mocker.Mock()
    RadioSystem.send_clearance.return_value = True

    with pytest.raises(ManualOverrideRequiredError):
        fc.authorize_takeoff(drone_id, battery_percent, flight_type, WeatherService, RadioSystem)

    WeatherService.get_current_wind_speed.assert_called_once()
    assert RadioSystem.send_clearance.call_count == 0   

def test_C(mocker):
    max_wind_speed_allowed = 15
    fc = FlightController(max_wind_speed_allowed)
    drone_id = "AA1234"
    battery_percent = 50
    flight_type = "COMMERCIAL"
    WeatherService = mocker.Mock()
    WeatherService.get_current_wind_speed.return_value = 10
    RadioSystem = mocker.Mock()
    RadioSystem.send_clearance.return_value = False

    with pytest.raises(CommunicationFailureError):
        fc.authorize_takeoff(drone_id, battery_percent, flight_type, WeatherService, RadioSystem)
    WeatherService.get_current_wind_speed.assert_called_once()
    RadioSystem.send_clearance.assert_called_once_with(drone_id)

def test_D(mocker):
    max_wind_speed_allowed = 15
    fc = FlightController(max_wind_speed_allowed)
    drone_id = "AA1234"
    battery_percent = 50
    flight_type = "COMMERCIAL"
    WeatherService = mocker.Mock()
    WeatherService.get_current_wind_speed.return_value = 10
    RadioSystem = mocker.Mock()
    RadioSystem.send_clearance.return_value = True

    clearance = fc.authorize_takeoff(drone_id, battery_percent, flight_type, WeatherService, RadioSystem)

    WeatherService.get_current_wind_speed.assert_called_once()
    RadioSystem.send_clearance.assert_called_once_with(drone_id)
    assert clearance == True