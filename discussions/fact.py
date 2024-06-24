

def fact(n):
    result = 1
    while n > 0:
        result *= n
        n -= 1

    return result

print(fact(5))

# python -m tokenize fact.py
# python -m ast fact.py

