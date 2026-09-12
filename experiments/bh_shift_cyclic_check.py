"""Exact four-ray germ calculation for the zigzag cyclic shift envelope.

Run on a remote CPU. This checks a finite affine quotient and an integer
lattice; the accompanying proof identifies the infinite permutation group.
"""

from collections import deque
from itertools import permutations, product
import json


def compose(f, g, modulus=None):
    """f after g; (sigma,t) sends (i,k) to (sigma[i], k+t[i])."""
    sigma = tuple(f[0][g[0][i]] for i in range(4))
    shift = tuple(g[1][i] + f[1][g[0][i]] for i in range(4))
    if modulus is not None:
        shift = tuple(t % modulus for t in shift)
    return sigma, shift


def determinant3(rows):
    a, b, c = rows
    return (a[0] * (b[1] * c[2] - b[2] * c[1])
            - a[1] * (b[0] * c[2] - b[2] * c[0])
            + a[2] * (b[0] * c[1] - b[1] * c[0]))


def main():
    identity = ((0, 1, 2, 3), (0, 0, 0, 0))
    alpha = ((2, 3, 0, 1), (0, -1, 1, 0))
    flip = ((1, 0, 3, 2), (0, 0, 0, 0))
    beta = ((0, 1, 2, 3), (0, 1, 0, -1))
    a = compose(alpha, alpha)
    b = beta
    c = compose(flip, compose(beta, flip))
    assert a == (identity[0], (1, -1, 1, -1))
    assert c == (identity[0], (1, 0, -1, 0))
    assert compose(compose(alpha, flip), compose(alpha, flip)) == identity

    vectors = [g[1] for g in (a, b, c)]
    # Coordinates in e1-e2, e2-e3, e3-e4 for the sum-zero lattice.
    coordinates = [tuple(sum(v[:j]) for j in (1, 2, 3)) for v in vectors]
    lattice_index = abs(determinant3(coordinates))
    assert lattice_index == 2
    for signs, expected in [((1, -1, 1), (2, -2, 0, 0)),
                            ((-1, 1, 1), (0, 2, -2, 0)),
                            ((1, 1, -1), (0, 0, 2, -2))]:
        assert tuple(sum(s * v[i] for s, v in zip(signs, vectors))
                     for i in range(4)) == expected

    ambient = {(p, t) for p in permutations(range(4))
               for t in product(range(2), repeat=4) if sum(t) % 2 == 0}
    seen = {identity}
    queue = deque([identity])
    while queue:
        element = queue.popleft()
        for generator in (alpha, flip, beta):
            neighbor = compose(element, generator, modulus=2)
            assert neighbor in ambient
            if neighbor not in seen:
                seen.add(neighbor)
                queue.append(neighbor)
    assert len(ambient) == 192 and len(seen) == 16
    assert len({g[0] for g in seen}) == 4
    assert len(ambient) // len(seen) == 12
    print(json.dumps({
        "origin": "exact remote CPU calculation; no GPU",
        "translation_vectors": vectors,
        "translation_lattice_index": lattice_index,
        "ambient_mod_2_order": len(ambient),
        "generated_mod_2_order": len(seen),
        "four_ray_index": 12,
        "scope": "finite germ quotient and lattice; infinite-group identification is in the proof",
    }, indent=2))


if __name__ == "__main__":
    main()
