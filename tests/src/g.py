def g(n):
    """
    g realiza operaciones sobre el parámetro n, devolviendo siempre el valor 1
    :param n: un número entero >= 1
    :return: devuelve siempre el valor 1 
    """
    while (n != 1):
        if (n % 2 == 0):
            n = n/2
        else:
            n = 3*n + 1
            
    return int(n)
