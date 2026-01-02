class CostCalculator:
    def __init__(self, distancia, nombre_turista, pesos_maletas):
        self.distancia = distancia
        self.nombre_turista = nombre_turista
        self.pesos_maletas = pesos_maletas

    def total_cost(self, discountService, additionalService):
        # CORREGIDO: Ajuste de límites según enunciado ("hasta 500")
        if 0 <= self.distancia <= 500:
            base_cost = 100
        elif 500 < self.distancia <= 2500:
            base_cost = 500
        elif self.distancia > 2500:
            base_cost = 900
        else:
            # Distancia negativa [cite: 98]
            raise Exception("Distancia incorrecta")
            
        discount_percentage = discountService.discount(self.nombre_turista)
        
        # Primero aplicamos descuento porcentual 
        price_with_discount = base_cost * (1 - (discount_percentage / 100.0))
        
        additional_cost = additionalService.cost(self.pesos_maletas)
        
        # Finalmente sumamos el coste de maletas [cite: 106]
        total = price_with_discount + additional_cost
        
        return total