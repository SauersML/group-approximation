"""Complete standard-library verifier; execute only on MSI, not locally.

Reconstructs the pinned Sym^4 matrices and every equation, verifies eigenbases,
and only then checks the 124 polynomial certificates. No Sage/Singular needed.
"""
from pathlib import Path
import json
import sys
import time

started = time.monotonic()
path = Path(sys.argv[1] if len(sys.argv)>1 else
            '/projects/standard/hsiehph/sauer354/hrf-breakthrough-2026-09-20-sym4/all-certificates.json')
bundle = json.loads(path.read_text())
ZERO, ONE, Z = (0, 0), (1, 0), (0, 1)
ZERO_EXPONENT = (0,)*9
VARIABLES = ['v1','v2','v3','v4','w1','w2','w3','w4','inv']


def add(x, y):
    return ((x[0]+y[0]) % 19, (x[1]+y[1]) % 19)


def neg(x):
    return ((-x[0]) % 19, (-x[1]) % 19)


def mul(x, y):
    a, b = x
    c, d = y
    return ((a*c-b*d) % 19, (a*d+b*c+4*b*d) % 19)


def power(x, n):
    answer = ONE
    while n:
        if n & 1:
            answer = mul(answer, x)
        x = mul(x, x)
        n //= 2
    return answer


def scalar(encoded):
    assert 0 <= len(encoded) <= 2
    assert all(isinstance(x, int) and 0 <= x < 19 for x in encoded)
    return tuple(encoded+[0]*(2-len(encoded)))


def identity():
    return [[ONE if i == j else ZERO for j in range(5)] for i in range(5)]


def matmul(X, Y):
    result = [[ZERO for _ in range(5)] for _ in range(5)]
    for i in range(5):
        for j in range(5):
            for h in range(5):
                result[i][j] = add(result[i][j], mul(X[i][h], Y[h][j]))
    return result


def inverse(X):
    rows = [list(row)+unit for row, unit in zip(X, identity())]
    for column in range(5):
        pivot = next((i for i in range(column, 5) if rows[i][column] != ZERO), None)
        assert pivot is not None, 'singular advertised eigenbasis'
        rows[column], rows[pivot] = rows[pivot], rows[column]
        reciprocal = power(rows[column][column], 359)
        assert mul(rows[column][column], reciprocal) == ONE
        rows[column] = [mul(x, reciprocal) for x in rows[column]]
        for i in range(5):
            if i != column:
                factor = rows[i][column]
                rows[i] = [add(x, neg(mul(factor, y)))
                           for x, y in zip(rows[i], rows[column])]
    assert [row[:5] for row in rows] == identity()
    answer = [row[5:] for row in rows]
    assert matmul(X, answer) == matmul(answer, X) == identity()
    return answer


def sym4(edge):
    # Independent construction by repeated polynomial multiplication,
    # rather than the generating script's binomial-coefficient formula.
    a, b, c, d = edge
    assert (a*d-b*c) % 19 == 1
    columns = []
    for i in range(5):
        coefficients = [1]
        for constant, linear in [(a,c)]*(4-i)+[(b,d)]*i:
            result = [0]*(len(coefficients)+1)
            for j, value in enumerate(coefficients):
                result[j] = (result[j]+constant*value) % 19
                result[j+1] = (result[j+1]+linear*value) % 19
            coefficients = result
        columns.append([(value, 0) for value in coefficients])
    return [[columns[j][i] for j in range(5)] for i in range(5)]


def p_add(X, Y):
    answer = dict(X)
    for exponent, coefficient in Y.items():
        value = add(answer.get(exponent, ZERO), coefficient)
        if value == ZERO:
            answer.pop(exponent, None)
        else:
            answer[exponent] = value
    return answer


def p_scale(X, coefficient):
    if coefficient == ZERO:
        return {}
    return {exponent: mul(value, coefficient) for exponent, value in X.items()}


def p_mul(X, Y):
    answer = {}
    for left, a in X.items():
        for right, b in Y.items():
            exponent = tuple(x+y for x, y in zip(left, right))
            value = add(answer.get(exponent, ZERO), mul(a, b))
            if value == ZERO:
                answer.pop(exponent, None)
            else:
                answer[exponent] = value
    return answer


def decode_polynomial(terms):
    answer = {}
    for powers, coefficient in terms:
        assert len(powers) == 9 and all(isinstance(n, int) and n >= 0 for n in powers)
        exponent = tuple(powers)
        value = scalar(coefficient)
        assert value != ZERO and exponent not in answer
        answer[exponent] = value
    return answer


def intertwiner(P, P_inverse, shift, offset):
    # P*T_shift*diag(1,x1,x2,x3,x4)*P^-1. The j-th column of
    # T_shift is e_(j-shift), so each coefficient is a rank-one product.
    result = [[{} for _ in range(5)] for _ in range(5)]
    for i in range(5):
        for j in range(5):
            for h in range(5):
                exponent = [0]*9
                if h:
                    exponent[offset+h-1] = 1
                coefficient = mul(P[i][(h-shift) % 5], P_inverse[h][j])
                if coefficient != ZERO:
                    result[i][j][tuple(exponent)] = coefficient
    return result


def polynomial_matmul(X, Y):
    result = [[{} for _ in range(5)] for _ in range(5)]
    for i in range(5):
        for j in range(5):
            for h in range(5):
                result[i][j] = p_add(result[i][j], p_mul(X[i][h], Y[h][j]))
    return result


metadata = bundle['input']
assert metadata['characteristic'] == 19 and metadata['field_order'] == 361
assert metadata['modulus'] == 'z^2-4*z+1'
assert metadata['domain'] == 'algebraic closure; no finite-field equations'
assert power(Z, 5) == ONE and Z != ONE
assert all((a*a-4*a+1) % 19 != 0 for a in range(19))
edges = [(2,11,16,3), (5,11,4,9), (6,15,12,8)]
A, B, C = [sym4(edge) for edge in edges]
for name, actual in zip(('A','B','C'), (A,B,C)):
    encoded = metadata[name]
    assert len(encoded) == 5 and all(len(row) == 5 for row in encoded)
    assert [[scalar(x) for x in row] for row in encoded] == actual, name
    fifth_power = identity()
    for _ in range(5):
        fifth_power = matmul(fifth_power, actual)
    assert fifth_power == identity(), name

eigenvalues = [power(Z, j) for j in range(5)]
assert len(set(eigenvalues)) == 5
diagonal = [[eigenvalues[i] if i == j else ZERO for j in range(5)] for i in range(5)]
bases, inverses = [], []
for name, actual in (('PB',B), ('PC',C)):
    encoded = metadata[name]
    assert len(encoded) == 5 and all(len(row) == 5 for row in encoded)
    P = [[scalar(x) for x in row] for row in encoded]
    P_inverse = inverse(P)
    assert matmul(actual, P) == matmul(P, diagonal), name
    bases.append(P)
    inverses.append(P_inverse)

V_choices = [intertwiner(bases[0], inverses[0], b, 0) for b in range(5)]
W_choices = [intertwiner(bases[1], inverses[1], c, 4) for c in range(5)]
products = {(b,c): polynomial_matmul(V_choices[b], W_choices[c])
            for b in range(5) for c in range(5)}
saturation = {(1,)*9: ONE, ZERO_EXPONENT: neg(ONE)}
certificates = bundle['certificates']
triples = [tuple(case['triple']) for case in certificates]
expected = {(a,b,c) for a in range(5) for b in range(5) for c in range(5) if a or b or c}
assert len(triples) == 124 and set(triples) == expected

for case in certificates:
    assert case['prime'] == 19 and case['quadratic_relation'] == 'z^2=4z-1'
    assert case['variables'] == VARIABLES
    assert len(case['equations']) == len(case['multipliers']) == 26
    a, b, c = case['triple']
    U = products[b,c]
    equations = []
    for i in range(5):
        for j in range(5):
            polynomial = {}
            for h in range(5):
                polynomial = p_add(polynomial, p_scale(U[i][h], A[h][j]))
                polynomial = p_add(polynomial, p_scale(U[h][j], neg(mul(eigenvalues[a], A[i][h]))))
            equations.append(polynomial)
    equations.append(saturation)
    advertised = [decode_polynomial(f) for f in case['equations']]
    assert advertised == equations, ('equation mismatch', case['triple'])
    total = {}
    for equation, multiplier in zip(equations, case['multipliers']):
        total = p_add(total, p_mul(equation, decode_polynomial(multiplier)))
    assert total == {ZERO_EXPONENT: ONE}, ('identity failure', case['triple'])

print('PASS', json.dumps({'certificates': len(certificates),
      'pinned_edges_reconstructed': True, 'sym4_matrices_matched': True,
      'eigenbases_invertible_and_verified': True,
      'all_3224_equations_reconstructed_and_matched': True,
      'all_124_nonzero_triples_covered': True, 'identity': 'sum(h_i*f_i)=1',
      'arithmetic': 'F19[z]/(z^2-4z+1)', 'elapsed_seconds': time.monotonic()-started}))
