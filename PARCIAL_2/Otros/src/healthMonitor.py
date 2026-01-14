class SensorReadError(Exception):
    """Custom exception for sensor read errors."""
    pass

class CriticalMonitorFailure(Exception):
    """Custom exception for critical monitor failures."""
    pass

class HealthMonitor:
    def __init__(self):
        pass

    def check_patient_status(self, patient_id, sensor_suite, notifier):
        battery_level = sensor_suite.get_battery_level()
        if battery_level < 20:
            try:
                hr = sensor_suite.read_heart_rate()
                if hr < 40 or hr > 140:
                    notifier.alert_doctor(patient_id, "HR_CRITICAL")
                    return "CRITICAL"
                else:
                    return "STABLE"

            except SensorReadError:
                raise(CriticalMonitorFailure())
        else:
            try:
                hr = sensor_suite.read_heart_rate()
                if hr < 40 or hr > 140:
                    notifier.alert_doctor(patient_id, "HR_CRITICAL")
                    return "CRITICAL"

            except SensorReadError:
                raise(CriticalMonitorFailure())
            
            try:
                o2 = sensor_suite.read_oxygen_saturation()
                if o2 < 90:
                    notifier.alert_nurse(patient_id, "O2_LOW")
                    return "WARNING"
                else:
                    return "STABLE"
            except SensorReadError:
                return "STABLE"