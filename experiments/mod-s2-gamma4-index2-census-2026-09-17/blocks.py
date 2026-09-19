"""For each Sp_4(F_2)-orbit of functionals chi on Gamma(4)/Gamma(8) = sp_4(F_2),
count the level-two splittings s = P + P^perp whose block subalgebra
sp(P) + sp(P^perp) (the image of Stab_{Gamma(4)}(x), x over s) chi kills.
Then Gamma(4)-orbits of splittings over s split in two under ker(chi)."""
import itertools
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import index2 as I  # noqa: E402

J2 = I.J % 2
vecs = [np.array(v) for v in itertools.product(range(2), repeat=4) if any(v)]


def span(gens):
    S = {(0, 0, 0, 0)}
    for g in gens:
        S |= {tuple((np.array(s) + g) % 2) for s in S}
    return S


def splittings():
    out = set()
    for a, b in itertools.combinations(vecs, 2):
        if (a @ J2 @ b) % 2 == 1:
            P = frozenset(span([a, b]))
            perp = [v for v in vecs if all((np.array(p) @ J2 @ v) % 2 == 0
                                           for p in P)]
            Q = frozenset(span(perp))
            out.add(frozenset([P, Q]))
    return sorted(out, key=lambda s: sorted(map(sorted, s)))


def block(s, R):
    P, Q = list(s)
    rows = []
    for c in itertools.product(range(2), repeat=len(R)):
        Ym = ((np.array(c) @ R) % 2).reshape(4, 4)
        if all(tuple((Ym @ np.array(v)) % 2) in P for v in P) and \
           all(tuple((Ym @ np.array(v)) % 2) in Q for v in Q):
            rows.append(np.array(c))
    return rows


def main():
    R = I.gamma48_basis()
    piv, reps = I.orbit_reps(R)
    S = splittings()
    assert len(S) == 10
    blocks = [block(s, R) for s in S]
    print("block sizes", [len(b) for b in blocks])
    for idx, (chi, size) in enumerate(reps):
        c = np.array(chi)
        killed = sum(all((c @ y) % 2 == 0 for y in b) for b in blocks)
        print(idx, chi, "orbit", size, "killed splittings", killed,
              "predicted classes", 160 + 16 * killed)


if __name__ == "__main__":
    main()
