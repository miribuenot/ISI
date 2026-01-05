class LowBatteryError(Exception):
    pass

class UnsafeWeatherError(Exception):
    pass

class ManualOverrideRequiredError(Exception):
    pass

class CommunicationFailureError(Exception):
    pass

class SensorOfflineException(Exception):
    pass

class FlightController:
    def __init__(self, max_wind_speed_allowed):
        self.max_wind_speed_allowed = max_wind_speed_allowed

    def authorize_takeoff(self, drone_id, battery_percent, flight_type, weather_service, radio_system):
        if battery_percent < 20:
            raise LowBatteryError()
        
        try:
            wind_speed = weather_service.get_current_wind_speed()
        except SensorOfflineException:
            raise ManualOverrideRequiredError()
        
        if flight_type != "EMERGENCY" and wind_speed > self.max_wind_speed_allowed:
            raise UnsafeWeatherError()
        elif flight_type == "EMERGENCY" and wind_speed > self.max_wind_speed_allowed * 2:
            raise UnsafeWeatherError()

        if not radio_system.send_clearance(drone_id):
            raise CommunicationFailureError()
        else:
            return True