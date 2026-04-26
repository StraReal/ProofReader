import math

externs = {
    'add':     lambda a, b: a + b,
    'sub':     lambda a, b: a - b,
    'neg':     lambda a: -a,
    'mul':     lambda a, b: a * b,
    'div':     lambda a, b: a // b,
    'fact':    lambda a: math.factorial(a),
    'lt':      lambda a, b: a < b,
    'gt':      lambda a, b: a > b,
    'eq_comp': lambda a, b: a == b,
    'and':     lambda a, b: a and b,
    'or':      lambda a, b: a or b,
    'exp':     lambda a, b: a ** b,
    'mod':     lambda a, b: a % b,
}