class AccessDeniedException(Exception):
    pass

class SecurityPolicyError(Exception):
    pass

class EmergencyLockdownException(Exception):
    pass

class HardwareMalfunctionException(Exception):
    pass

class NetworkException(Exception):
    pass

class DoorController:
    def __init__(self, region):
        self.region = region

    def attempt_access(self, card_id, pin, auth_service, lock_mechanism):
        if card_id == "" or pin == "":
            raise ValueError("Card ID and PIN must be provided.")
        elif len(pin) < 6 and self.region == "TOP-SECRET":
            raise SecurityPolicyError("PIN too short for TOP-SECRET region.")

        
        try:
            if not auth_service.verify(card_id, pin, self.region):
                raise AccessDeniedException("Access denied: invalid credentials.")
        except NetworkException:
            raise

        try:
            lock_mechanism.unlock()
        except HardwareMalfunctionException:
            raise EmergencyLockdownException("Emergency lockdown due to hardware malfunction.")

        return True