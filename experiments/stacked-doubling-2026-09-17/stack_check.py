#!/usr/bin/env python3
"""Sanity check for research/stacked-models-doubling-tower-proof.md.

Explicit stacked model with F = (Z/2)^N (elements = N-bit integers), P = N + 1 levels,
Pi_m = (Z/2)^m = span of the first m coordinates, and a compressor s of level shift a = 1
acting as the identity on F (so c_x(Pi_m) = Pi_m <= Pi_(m+1): strict doubling at every
interior level), wrapping level N to level 0.

Y = Z/(N+1) x F, point (m, f) encoded as m * 2^N + f.
Checks, by explicit permutations:
  * each generator sigma(l_i) (translation by e_i at levels m > i) preserves every cell,
    and the cells {m} x (f + Pi_m) are exactly the <S_L>-orbits;
  * sigma(s) maps every interior cell into a single cell of twice the size;
  * dominant targets and loss computed from the definition give
      sum ell = 2^N - 1,  lambda = (2^N - 1) / ((N+1) 2^N),
      lambda log|F| = N log 2 / (N+1) * (1 - 2^-N)  -> log 2;
  * the upper bound (UP) with |a| = 1 holds.
"""
import math
from collections import Counter


def check(N):
    P = N + 1
    Fsz = 1 << N
    Ysz = P * Fsz

    def mask(m):
        return (1 << m) - 1  # Pi_m = vectors supported on the first m coordinates

    def cell(y):
        m, f = divmod(y, Fsz)
        return (m, f & ~mask(m))  # coset representative of f + Pi_m

    # generators of L: l_i acts at level m by translation by e_i if i < m, else trivially
    gens = []
    for i in range(N):
        perm = [0] * Ysz
        for y in range(Ysz):
            m, f = divmod(y, Fsz)
            perm[y] = m * Fsz + ((f ^ (1 << i)) if i < m else f)
        gens.append(perm)

    # orbits of <S_L> by union-find
    parent = list(range(Ysz))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for perm in gens:
        for y in range(Ysz):
            assert cell(perm[y]) == cell(y), "generator leaves a cell"
            a, b = find(y), find(perm[y])
            if a != b:
                parent[a] = b
    orbit_cells = {}
    for y in range(Ysz):
        orbit_cells.setdefault(find(y), set()).add(cell(y))
    assert all(len(v) == 1 for v in orbit_cells.values()), "orbit meets two cells"
    assert len(orbit_cells) == len({cell(y) for y in range(Ysz)}), "cell split into orbits"

    # compressor s: level m -> m+1 mod P, identity on F
    s = [((y // Fsz + 1) % P) * Fsz + (y % Fsz) for y in range(Ysz)]
    assert sorted(s) == list(range(Ysz))

    cells = {}
    for y in range(Ysz):
        cells.setdefault(cell(y), []).append(y)
    total_loss = 0
    for c, pts in cells.items():
        cnt = Counter(cell(s[y]) for y in pts)
        tgt, hit = cnt.most_common(1)[0]
        ell = len(pts) - hit
        total_loss += ell
        if c[0] < N:  # interior: whole image in one cell of twice the size
            assert ell == 0 and len(cells[tgt]) == 2 * len(pts)
        else:  # wrap level: image spread over singletons
            assert ell == Fsz - 1
    assert total_loss == Fsz - 1
    lam = total_loss / Ysz
    assert abs(lam - (Fsz - 1) / (P * Fsz)) < 1e-15
    val = lam * math.log(Fsz)
    pred = N * math.log(2) / (N + 1) * (1 - 2.0 ** (-N))
    assert abs(val - pred) < 1e-12
    assert lam * math.log(Ysz) <= (math.log(P) + math.log(Fsz)) / P + 1e-12
    return lam, val, lam * math.log(Ysz)


if __name__ == "__main__":
    print(" N   lambda        lambda*log|F|  lambda*log|Y|  (log 2 = %.6f)" % math.log(2))
    for N in range(1, 13):
        lam, v, w = check(N)
        print("%2d  %.8f   %.8f     %.8f" % (N, lam, v, w))
    print("all checks passed")
