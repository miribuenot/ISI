def dos_menores(a = None):
    if type(a) != list or len(a) < 1:
        return None

    min1 = 0
    min2 = 0
    
    min1 = a[0]
    if len(a) == 1:
        return min1
    else:
        e = a[1]                       #1
        if (e < min1):
            min2 = min1
            min1 = e
        else:
            min2 = e

        for i in range(2, len(a)):
            e = a[i]
            if e < min1:
                min2 = min1
                min1 = e
            elif e < min2:
                min2 = e

    return min1, min2


    

