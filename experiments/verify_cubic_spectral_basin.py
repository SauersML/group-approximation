"""Exact finite calibrations for the cubic spectral basin.

The dimension-independent theorem is proved in the research Markdown.
These checks certify a rational-grid instance and the endpoint countermodel;
they are not substitutes for the proof over arbitrary real eigenangles.
Run with Python 3; no external packages are required.
"""

from fractions import Fraction


def recurrent_vertices(vertices, edges):
    """Vertices on directed cycles, computed by exact finite reachability."""
    recurrent = set()
    for source in vertices:
        pending = list(edges[source])
        visited = set()
        while pending:
            node = pending.pop()
            if node == source:
                recurrent.add(source)
                break
            if node not in visited:
                visited.add(node)
                pending.extend(edges[node])
    return recurrent


def main():
    denominator = 120
    a = Fraction(3, 8)
    epsilon = Fraction(1, denominator)
    assert epsilon < (2 - 5 * a) / 10
    vertices = set(range(-45, 46))
    edges = {}
    for vertex in vertices:
        successors = set()
        for error in (-1, 0, 1):
            successor = (2 * vertex + error + 60) % 120 - 60
            if successor in vertices:
                successors.add(successor)
        edges[vertex] = successors
    recurrent = recurrent_vertices(vertices, edges)
    expected = {-41, -40, -39, -1, 0, 1, 39, 40, 41}
    assert recurrent == expected, (recurrent, expected)
    assert all(min(abs(x - center) for center in (-40, 0, 40)) <= 1
               for x in recurrent)
    print("Recurrent grid numerators / 120:", sorted(recurrent))

    # U e_j = zeta**j e_j, V e_j = e_(3j mod 5).
    # V^* e_j = e_(2j mod 5), so V U V^* e_j = zeta**(2j) e_j.
    labels = {1, 2, 3, 4}
    permutation = {j: 3 * j % 5 for j in labels}
    assert set(permutation.values()) == labels
    assert all(permutation[2 * j % 5] == j for j in labels)
    phases = {Fraction(j if j <= 2 else j - 5, 5) for j in labels}
    assert max(map(abs, phases)) == Fraction(2, 5)
    assert all(3 * j % 5 != 0 for j in labels)
    print("Exact fifth-root phases:", sorted(phases))

    # Bookkeeping for the fixed torsion powers 3 -> 7 -> 127 -> N.
    exponent, defect, cubic_error = 3, 0, 1
    for _ in range(3):
        next_exponent = 2**exponent - 1
        defect = next_exponent + 2 * defect
        cubic_error *= 2
        exponent = next_exponent
    n = 2**127 - 1
    assert (exponent, defect, cubic_error) == (n, n + 282, 8)
    seed_defect = n + 2 * defect
    seed_cubic = n + 2 * cubic_error + 1
    assert (seed_defect, seed_cubic) == (3 * n + 564, n + 17)
    assert 8 * seed_defect + 7 == 24 * n + 4519
    assert 8 * seed_cubic == 8 * (n + 17)
    print("All exact arithmetic checks passed.")


if __name__ == "__main__":
    main()
