#!/usr/bin/env python3
"""Exact finite regressions for the QPCP full-target continuation.

Adapted from the user's supplied A.10. These check identities and examples,
not universal proofs or a constant-locality QPCP reduction. Standard library
only; every assertion uses integers or fractions.Fraction.
"""
from fractions import Fraction as F
from itertools import combinations, product
import json


def eye(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def zero(n):
    return [[F(0) for _ in range(n)] for _ in range(n)]


def transpose(a):
    return [list(row) for row in zip(*a)]


def add(a, b):
    return [[x + y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def scale(c, a):
    return [[c * x for x in row] for row in a]


def mul(a, b):
    bt = transpose(b)
    return [[sum((x * y for x, y in zip(ar, bc)), F(0))
             for bc in bt] for ar in a]


def kron(a, b):
    return [[x * y for x in ar for y in br] for ar in a for br in b]


def trace(a):
    return sum((a[i][i] for i in range(len(a))), F(0))


def outer(v, w):
    return [[x * y for y in w] for x in v]


I = eye(2)
X = [[F(0), F(1)], [F(1), F(0)]]
Z = [[F(1), F(0)], [F(0), F(-1)]]


def record_tests():
    a = kron(Z, kron(Z, I))
    b = kron(X, kron(I, Z))
    s = add(a, b)
    assert mul(s, s) == scale(2, eye(8))
    classical = add(scale(F(1, 2), eye(8)), scale(F(-1, 4), s))
    centered = add(classical, scale(F(-1, 2), eye(8)))
    assert mul(centered, centered) == scale(F(1, 8), eye(8))
    az, bx = kron(Z, Z), kron(X, X)
    quantum = add(scale(F(1, 2), eye(4)), scale(F(-1, 4), add(az, bx)))
    bell = [F(1), F(0), F(0), F(1)]  # unnormalized null-vector check
    assert all(sum((row[j] * bell[j] for j in range(4)), F(0)) == 0
               for row in quantum)
    qx = add(scale(F(3, 5), Z), scale(F(4, 5), X))
    assert mul(qx, qx) == I
    commutator = add(mul(Z, qx), scale(-1, mul(qx, Z)))
    assert mul(transpose(commutator), commutator) == scale(F(64, 25), I)
    s2 = add(kron(Z, Z), kron(X, qx))
    square = mul(s2, s2)
    assert square == add(scale(2, eye(4)), kron(mul(Z, X), commutator))
    p = add(square, scale(F(-18, 5), eye(4)))
    q = add(square, scale(F(-2, 5), eye(4)))
    assert mul(p, q) == zero(4)
    return 3


def coherent_phase_tests():
    checked = []
    for n in range(1, 7):
        mask = (1 << n) - 1
        functions = {
            'parity': lambda x: x.bit_count() % 2,
            'and': lambda x, mask=mask: int(x == mask),
            'constant': lambda x: 0,
        }
        for name, f in functions.items():
            encoded = [(x << 1) | f(x) for x in range(1 << n)]
            density = {(u, v): F(1, 1 << n) for u in encoded for v in encoded}
            energy = F(0)
            for i in range(n):
                x_expectation = sum((density.get((u ^ (1 << (i + 1)), u), F(0))
                                     for u in encoded), F(0))
                energy += (1 - x_expectation) / (2 * n)
            sensitivity = sum(f(x) != f(x ^ (1 << i))
                              for x in range(1 << n) for i in range(n))
            assert energy == F(sensitivity, 2 * n * (1 << n))
            expected = {'parity': F(1, 2), 'and': F(1, 1 << n), 'constant': F(0)}[name]
            assert energy == expected
            checked.append({'n': n, 'record': name, 'phase_energy': str(energy)})
    return checked


def nonorthogonal_phase_tests():
    # Rational unit vectors give exact positive, zero, and negative overlaps.
    vectors = ((F(1), F(0)), (F(3, 5), F(4, 5)),
               (F(0), F(1)), (F(-3, 5), F(4, 5)))
    cases = 0
    for u, v in product(vectors, repeat=2):
        overlap = sum(x * y for x, y in zip(u, v))
        density = scale(F(1, 2), outer(u + v, u + v))
        phase = kron(scale(F(1, 2), add(I, scale(-1, X))), I)
        energy = trace(mul(phase, density))
        assert energy == (1 - overlap) / 2
        s_squared = 1 - overlap**2
        difference = add(outer(u, u), scale(-1, outer(v, v)))
        assert mul(difference, difference) == scale(s_squared, I)
        assert energy >= (1 - abs(overlap)) / 2
        if energy <= F(1, 2):
            assert s_squared <= 4 * energy * (1 - energy)
        cases += 1
    # A two-bit, nonorthogonal vector-valued record checks C3 directly.
    n, records = 2, vectors
    vec = tuple(x for record in records for x in record)
    density = scale(F(1, 4), outer(vec, vec))
    energy = F(0)
    for bit in range(n):
        flip = [[F(j == (i ^ (1 << (bit + 1)))) for j in range(8)]
                for i in range(8)]
        energy += (1 - trace(mul(flip, density))) / (2 * n)
    distance_sum = sum((sum((x - y)**2 for x, y in
                           zip(records[label], records[label ^ (1 << bit)]))
                        for label in range(4) for bit in range(n)), F(0))
    assert energy == distance_sum / (4 * n * 4)
    return cases + 1


def encoded_support_tests():
    code = [int(''.join(bit * 3 for bit in f'{x:02b}'), 2) for x in range(4)]
    tests = 0
    for x, y in combinations(code, 2):
        assert (x ^ y).bit_count() >= 3
        for size in range(3):
            for region in combinations(range(6), size):
                mask = sum(1 << j for j in region)
                assert (x ^ y) & ~mask
                tests += 1
    return tests


def ghz_and_leakage_tests():
    # Enumerate a real matrix-unit basis for every <=2-site data operator.
    # A complex operator is a complex linear combination of the same units.
    plus, minus = [F(0)] * 8, [F(0)] * 8
    plus[0] = plus[7] = minus[0] = F(1)
    minus[7] = F(-1)
    rho_plus, rho_minus = scale(F(1, 2), outer(plus, plus)), scale(F(1, 2), outer(minus, minus))
    cases = 0
    for size in range(3):
        for region in combinations(range(3), size):
            mask = sum(1 << i for i in region)
            for row, col in product(range(1 << size), repeat=2):
                matrix = zero(8)
                for x, y in product(range(8), repeat=2):
                    xr = sum(((x >> bit) & 1) << j for j, bit in enumerate(region))
                    yr = sum(((y >> bit) & 1) << j for j, bit in enumerate(region))
                    matrix[x][y] = F(xr == row and yr == col and (x & ~mask) == (y & ~mask))
                assert matrix[0][7] == matrix[7][0] == 0
                assert trace(mul(matrix, rho_plus)) == trace(mul(matrix, rho_minus))
                cases += 1
    target = scale(F(1, 2), add(I, scale(-1, X)))
    error = add(scale(F(1, 2), I), scale(-1, target))
    assert mul(error, error) == scale(F(1, 4), I)
    # Code span |000>,|111>; retained mass 9/25. K is a positive rank-one
    # effect coupling the code to |001>, with label-diagonal compression.
    psi, effect_vector = [F(0)] * 8, [F(0)] * 8
    psi[0], psi[1] = F(3, 5), F(4, 5)
    effect_vector[0], effect_vector[1] = F(1), F(1)
    rho = outer(psi, psi)
    effect = scale(F(1, 2), outer(effect_vector, effect_vector))
    sigma = zero(8)
    sigma[0][0] = F(1)
    delta = F(16, 25)
    assert mul(effect, effect) == effect
    change = trace(mul(effect, add(rho, scale(-1, sigma))))
    assert change**2 <= delta
    return {'ghz_matrix_units': cases, 'sharp_norm_example': True,
            'leakage_example': {'delta': str(delta), 'energy_change': str(change)}}


def choi_tests():
    counts = []
    real_paulis = (I, X, Z, mul(X, Z))
    for n in (1, 2):
        dimension = 1 << n
        unitaries = []
        for letters in product(real_paulis, repeat=n):
            u = [[F(1)]]
            for letter in letters:
                u = kron(u, letter)
            assert mul(transpose(u), u) == eye(dimension)
            unitaries.append(u)
        projectors, total = [], zero(dimension**2)
        for u in unitaries:
            vec = [u[k][j] for j in range(dimension) for k in range(dimension)]
            p = scale(F(1, dimension), outer(vec, vec))
            assert mul(p, p) == p and trace(p) == 1
            partial = [[sum((p[j * dimension + k][ell * dimension + k]
                             for k in range(dimension)), F(0))
                        for ell in range(dimension)] for j in range(dimension)]
            assert partial == scale(F(1, dimension), eye(dimension))
            projectors.append(p)
            total = add(total, p)
        assert total == eye(dimension**2)
        effects = []
        for i in range(dimension**2):
            p = zero(dimension**2)
            p[i][i] = F(1)
            effects.append(p)
        effects += projectors
        for effect in effects:
            valid = [trace(mul(effect, p)) for p in projectors]
            invalid = [effect[i][i] for i in range(dimension**2)]
            average = trace(effect) / dimension**2
            assert sum(valid, F(0)) / dimension**2 == average
            assert sum(invalid, F(0)) / dimension**2 == average
            assert min(invalid) <= average <= max(valid)
        marginal_difference = [1 - F(1, dimension)] + [-F(1, dimension)] * (dimension - 1)
        assert sum(abs(x) for x in marginal_difference) / 2 == 1 - F(1, dimension)
        counts.append({'input_dimension': dimension, 'unitary_choi_states': len(projectors),
                       'effects_checked': len(effects)})
    return counts


def perturbative_support_tests():
    results = []
    for n in range(2, 9):
        target = (1 << n) - 1

        def walls(mask):
            return sum(((mask >> i) & 1) != ((mask >> (i + 1)) & 1)
                       for i in range(n - 1))

        states, amplitudes = {0: F(1)}, []
        for order in range(1, n + 1):
            transitioned = {}
            for mask, amp in states.items():
                for i in range(n):
                    new = mask ^ (1 << i)
                    transitioned[new] = transitioned.get(new, F(0)) + amp
            final_amp = transitioned.get(target, F(0))
            amplitudes.append(final_amp)
            if order < n:
                assert final_amp == 0
            states = {mask: amp / walls(mask) for mask, amp in transitioned.items()
                      if mask not in (0, target)}
        assert amplitudes[-1] == 2**(n - 1)
        results.append({'repetition_length': n, 'first_nonzero_order': n,
                        'unsigned_path_sum': str(amplitudes[-1]),
                        'signed_effective_coefficient': str((-1)**(n - 1) * amplitudes[-1])})
    # Independent exact two-bit Schur calculation at z=0, Delta=4, V=X1+X2.
    # ||V||=2<4, QVQ=0; the complement inverse is I/4.
    v_matrix = add(kron(X, I), kron(I, X))
    p_indices, q_indices = (0, 3), (1, 2)
    coupling = [[v_matrix[i][j] for j in q_indices] for i in p_indices]
    effective = scale(F(-1, 4), mul(coupling, transpose(coupling)))
    assert effective[0][1] == F(-1, 2)
    v, a, r = F(2), F(4), 2
    bound = v * (v / a)**(r - 1) / (1 - v / a)
    assert abs(effective[0][1]) <= bound
    return results


def main():
    result = {
        'arithmetic': 'exact integers and fractions.Fraction',
        'shared_record_operator_identities': record_tests(),
        'coherent_phase_cases': coherent_phase_tests(),
        'nonorthogonal_phase_cases': nonorthogonal_phase_tests(),
        'encoded_support_cases': encoded_support_tests(),
        'ghz_and_leakage_cases': ghz_and_leakage_tests(),
        'choi_cases': choi_tests(),
        'perturbative_cases': perturbative_support_tests(),
        'convergent_schur_sign_example': True,
        'all_checks_passed': True,
        'scope': 'Finite checks of identities and counterexamples; no full QPCP reduction.',
    }
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
