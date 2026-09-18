"""Brute-force checks for ug-hardness-deficit-ratio-padding-line (items 1 and 5).

Games are bipartite with left vertices 0..nl-1, right 0..nr-1, alphabet Z_m.
A proper d-to-d linear constraint on (x_u, y_v) is {y = x + b_t : t < d} with
distinct shifts b_t, so the branches are pointwise distinct permutations.
Checks, for every labeling, exact rational identities:
  * val_x(Split G) == E_e 1[x satisfies e] / d_e, and val(Split G) <= 1/2;
  * val(P_lambda(U)) == lambda + (1 - lambda) val(U), with the padded game built
    literally (scaled weights plus one identity edge on a new vertex pair).
"""
import itertools
import random
from fractions import Fraction


def game_value(nl, nr, m, edges):
    """edges: list of (u, v, w, perm); exact max satisfied weight fraction."""
    total = sum(w for _, _, w, _ in edges)
    best = Fraction(0)
    for lab in itertools.product(range(m), repeat=nl + nr):
        sat = sum(w for u, v, w, p in edges if lab[nl + v] == p[lab[u]])
        best = max(best, Fraction(sat, total))
    return best


def check_instance(rng):
    m = rng.choice([3, 4, 5])
    nl, nr = rng.choice([(2, 1), (2, 2), (1, 3)])
    cons = []
    for _ in range(rng.randint(2, 5)):
        d = rng.choice([2, 3])
        shifts = rng.sample(range(m), d)
        cons.append((rng.randrange(nl), rng.randrange(nr), rng.randint(1, 4), shifts))
    W = sum(w for _, _, w, _ in cons)
    L = 6  # lcm of arities 2 and 3
    split = [(u, v, w * L // len(sh), tuple((a + b) % m for a in range(m)))
             for u, v, w, sh in cons for b in sh]
    for lab in itertools.product(range(m), repeat=nl + nr):
        sat_split = sum(w for u, v, w, p in split if lab[nl + v] == p[lab[u]])
        lhs = Fraction(sat_split, L * W)
        rhs = sum(Fraction(w, W) * Fraction(int((lab[nl + v] - lab[u]) % m in sh), len(sh))
                  for u, v, w, sh in cons)
        assert lhs == rhs, (lab, lhs, rhs)
    val_split = game_value(nl, nr, m, split)
    assert val_split <= Fraction(1, 2)
    p, q = rng.randint(1, 4), 5
    lam = Fraction(p, q)
    w_split = sum(w for _, _, w, _ in split)
    ident = tuple(range(m))
    padded = [(u, v, w * (q - p), perm) for u, v, w, perm in split]
    padded.append((nl, nr, p * w_split, ident))
    val_pad = game_value(nl + 1, nr + 1, m, padded)
    assert val_pad == lam + (1 - lam) * val_split, (val_pad, lam, val_split)
    return val_split, lam, val_pad


if __name__ == "__main__":
    rng = random.Random(20260918)
    for _ in range(40):
        check_instance(rng)
    print("OK: 40 random instances; split identity labeling-by-labeling, "
          "val(Split) <= 1/2, padding identity exact")
