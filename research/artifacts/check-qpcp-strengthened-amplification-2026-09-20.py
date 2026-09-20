#!/usr/bin/env python3
"""Exact finite regressions for the September 20 QPCP refinement.

Adapted from Appendix A of the supplied proof development. Matrix helpers
come from Cairn's September 11 replay. These examples supplement the
written universal proofs; they do not construct a locality reducer.
"""
from collections import deque
from fractions import Fraction as F
from functools import reduce
from hashlib import sha256
from itertools import product
import json


def eye(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def transpose(a):
    return [list(row) for row in zip(*a)]


def multiply(a, b):
    columns = transpose(b)
    return [[sum((x * y for x, y in zip(row, col)), F(0))
             for col in columns] for row in a]


def scale(c, a):
    return [[c * x for x in row] for row in a]


def add(a, b):
    return [[x + y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def subtract(a, b):
    return add(a, scale(-1, b))


def tensor(a, b):
    return [[x * y for x in ar for y in br] for ar in a for br in b]


def ldl_psd(a):
    """Return and replay an exact unpivoted LDL certificate of A >= 0."""
    assert a == transpose(a)
    n = len(a)
    lower, diagonal = eye(n), [F(0)] * n
    for j in range(n):
        diagonal[j] = a[j][j] - sum(
            (lower[j][k] ** 2 * diagonal[k] for k in range(j)), F(0))
        assert diagonal[j] >= 0, (j, diagonal[j])
        for i in range(j + 1, n):
            residual = a[i][j] - sum(
                (lower[i][k] * lower[j][k] * diagonal[k]
                 for k in range(j)), F(0))
            if diagonal[j] == 0:
                assert residual == 0
            else:
                lower[i][j] = residual / diagonal[j]
    diag_matrix = [[diagonal[i] if i == j else F(0)
                    for j in range(n)] for i in range(n)]
    assert multiply(multiply(lower, diag_matrix), transpose(lower)) == a
    return [str(x) for x in diagonal]


def digest(a):
    raw = json.dumps([[str(x) for x in row] for row in a], separators=(",", ":"))
    return sha256(raw.encode()).hexdigest()


def regular_graph(degree: int, vertices: int) -> list[tuple[int, int]]:
    if degree < 2 or vertices <= degree or vertices % 2:
        raise ValueError('Need degree >= 2, an even vertex count > degree.')
    edges = set()
    for v in range(vertices):
        for step in range(1, degree // 2 + 1):
            w = (v + step) % vertices
            edges.add(tuple(sorted((v, w))))
        if degree % 2:
            edges.add(tuple(sorted((v, (v + vertices // 2) % vertices))))
    out = sorted(edges)
    assert all(sum(v in e for e in out) == degree for v in range(vertices))
    return out


def single_defect_tests(degree: int, vertices: int) -> int:
    edges = regular_graph(degree, vertices)
    adj = [[] for _ in range(vertices)]
    for i, (v, w) in enumerate(edges):
        adj[v].append((w, i))
        adj[w].append((v, i))
    parents = {0: (-1, -1)}
    queue = deque([0])
    while queue:
        v = queue.popleft()
        for w, edge in adj[v]:
            if w not in parents:
                parents[w] = (v, edge)
                queue.append(w)
    assert len(parents) == vertices
    defects = [0] * vertices
    for target in range(vertices):
        assignment = [0] * len(edges)
        v = target
        while v != 0:
            parent, edge = parents[v]
            assignment[edge] ^= 1
            v = parent
        observed = []
        for v in range(vertices):
            parity = sum(assignment[i] for _, i in adj[v]) % 2
            if parity != int(v == 0):
                observed.append(v)
                defects[v] += 1
        assert observed == [target]
    assert defects == [1] * vertices
    if len(edges) <= 18:
        minimum = vertices
        for mask in range(1 << len(edges)):
            count = sum((sum((mask >> i) & 1 for _, i in adj[v]) % 2)
                        != int(v == 0) for v in range(vertices))
            minimum = min(minimum, count)
        assert minimum == 1
    return vertices


def sharper_walk_tests() -> list[dict]:
    """Full operator inequalities, including an indefinite walk matrix."""
    identity = eye(2)
    h = [[[F(1), F(0)], [F(0), F(0)]],
         [[F(9, 25), F(12, 25)], [F(12, 25), F(16, 25)]]]
    q = [subtract(identity, term) for term in h]
    assert all(multiply(term, term) == term for term in h + q)
    assert multiply(h[0], h[1]) != multiply(h[1], h[0])
    epsilon = F(1, 5)
    shifted = subtract(scale(F(1, 2), add(*h)), scale(epsilon, identity))
    ldl_psd(shifted)
    assert shifted[0][0] * shifted[1][1] == shifted[0][1] ** 2
    results = []
    for stay in (F(1, 4), F(1, 2), F(3, 4)):
        transition = [[stay, 1-stay], [1-stay, stay]]
        eigenvalue = 2*stay - 1
        lam = abs(eigenvalue)
        for t in range(2, 5):
            dimension = 2**t
            acceptance = scale(0, eye(dimension))
            total = F(0)
            for walk in product(range(2), repeat=t):
                weight = F(1, 2)
                for j in range(t-1):
                    weight *= transition[walk[j]][walk[j+1]]
                total += weight
                term = reduce(tensor, (q[v] for v in walk))
                acceptance = add(acceptance, scale(weight, term))
            assert total == 1
            gap = 1-(1-epsilon)*(1-(1-lam)*epsilon)**(t-1)
            slack = subtract(scale(1-gap, eye(dimension)), acceptance)
            pivots = ldl_psd(slack)
            if stay == F(3, 4) and t == 4:
                assert gap == F(521, 1250)
                assert digest(acceptance) == (
                    'ab80b435a5c3f8ade43f223cfc0914a1ac773884e1e900758df5d7492a920dd7')
            results.append({'nontrivial_eigenvalue': str(eigenvalue),
                            'walk_vertices': t, 'dimension': dimension,
                            'certified_gap': str(gap),
                            'acceptance_sha256': digest(acceptance),
                            'gap_slack_ldl_diagonal': pivots,
                            'positive_ldl_pivots': sum(F(v) > 0 for v in pivots)})
    return results


def main() -> None:
    graph_cases = witnesses = 0
    for degree in range(2, 11):
        first = degree + 1 + ((degree + 1) % 2)
        for vertices in (first, first + 2, first + 8):
            witnesses += single_defect_tests(degree, vertices)
            graph_cases += 1
    grid_cases = 0
    for t in range(2, 66, 2):
        s = (t - 2) // 2
        B = F(3*t + 2, 8)
        for j in range(101):
            x = F(j, 100)
            exact_bound = 1-(1-x)*(1-F(3, 4)*x)**s
            assert exact_bound >= B*x/(1+B*x)
            grid_cases += 1
    sharper_grid_cases = 0
    for t in range(2, 66):
        B = F(t+1, 2)
        for j in range(101):
            x = F(j, 100)
            sharp_bound = 1-(1-x)*(1-x/2)**(t-1)
            assert sharp_bound >= B*x/(1+B*x)
            if t % 2 == 0:
                old_bound = 1-(1-x)*(1-F(3, 4)*x)**((t-2)//2)
                assert sharp_bound >= old_bound
            sharper_grid_cases += 1
    operator_results = sharper_walk_tests()
    B, loss, q = F(11, 2), F(5), 1024
    theta = loss/B
    rounds = 0
    while theta**rounds*q > 1:
        rounds += 1
    energy = F(1, q)
    for j in range(rounds):
        energy = B*energy/(loss*(1+B*energy))
        formula = 1/(theta**(j+1)*q + loss*(1-theta**(j+1))/(1-theta))
        assert energy == formula
    floor = 1/(1+loss/(1-theta))
    assert floor == F(1, 56) and rounds == 73 and energy >= floor
    print(json.dumps({
        'arithmetic': 'exact integers and fractions.Fraction',
        'regular_graph_cases': graph_cases,
        'single_defect_witnesses': witnesses,
        'original_rational_grid_cases': grid_cases,
        'sharper_rational_grid_cases': sharper_grid_cases,
        'sharper_full_operator_cases': len(operator_results),
        'operator_results': operator_results,
        'example': {'walk_vertices': 10, 'B': str(B), 'loss': str(loss),
                    'seed_energy': '1/1024', 'rounds': rounds,
                    'certified_constant_floor': str(floor),
                    'recurrence_energy_decimal_for_display': float(energy)},
        'all_checks_passed': True,
        'scope': 'Finite regression only; universal claims use written proofs.'
    }, indent=2))


if __name__ == '__main__':
    main()
