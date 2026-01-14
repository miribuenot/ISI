class ServiceUnavailableError(Exception):
    pass

class InsufficientFundsError(Exception):
    pass

class AccountFrozenError(Exception):
    pass

class TransactionManager:
    def __init__(self):
        pass

    def process_batch(self, transactions_ids, fraud_detector, bank_gateway):
        
        if type(transactions_ids) is not list:
            raise ValueError("transactions_ids must be a list")
        elif len(transactions_ids) == 0:
            raise ValueError("transactions_ids cannot be empty")
        

        result = { "success": [], "failed": [] }

        for tx_id in transactions_ids:
            try:
                if fraud_detector.check(tx_id):
                    bank_gateway.transfer(tx_id)
                    result["success"].append(tx_id)
                else:
                    result["failed"].append(tx_id)
            except Exception as e:
                if isinstance(e, (InsufficientFundsError)):
                    result["failed"].append(tx_id)
                else:
                    raise e

        return result