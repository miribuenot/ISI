class InvalidArgument(Exception):
    "Function called with invalid arguments"
    pass


def max_dist(numbers=None):
    if not isinstance(numbers, list) or len(numbers) == 0:
        raise InvalidArgument()

    for num in numbers:
        if not isinstance(num, int):
            raise TypeError("All elements in the list must be numbers.")

    return abs(max(numbers) - min(numbers))