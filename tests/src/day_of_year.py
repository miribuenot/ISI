class InvalidArgument(Exception):
    "Function called with invalid arguments"
    pass

def is_leap_year(year):
    return year % 4 == 0 and (year % 100 != 0 or year % 400 == 0)

def day_of_year(day=None, month=None, year=None):
    if day is None or month is None or year is None:
        raise InvalidArgument()

    # Check for valid date ranges
    if not (1 <= month <= 12):
        raise InvalidArgument("Month must be between 1 and 12.")
    
    
    # Days in each month
    days_in_month = [31, 28 + is_leap_year(year), 31, 30, 31, 30,
                     31, 31, 30, 31, 30, 31]
    
    if not (1 <= day <= days_in_month[month - 1]):
        raise InvalidArgument(f"Day must be between 1 and {days_in_month[month - 1]} for month {month}.")

    # Calculate the day of the year
    day_of_year = sum(days_in_month[:month - 1]) + day
    return day_of_year