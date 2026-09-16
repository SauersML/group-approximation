#!/usr/bin/env python3
"""Relative-torsion (non-purity) search for planar Rips complexes.

For a finite planar set G, scale r and subset A of G, the image of
H_2(R_r(A)) -> H_2(R_r(G)) is pure iff H_2(R_r(G), R_r(A)) is torsion-free
(the kernel of H_1(R(A)) -> H_1(R(G)) is free, so torsion of the relative group
equals torsion of the cokernel).  A "multiplying chain gadget" (see
research/some-planar-rips-chain-gadget-multiplies-a-sphere-class.md) needs a
non-pure image.  The relative complex is modelled by the cofibre
R(G) u cone(R(A)), which is the clique complex of the r-graph on G plus one
abstract vertex joined to A.  We reduce by dominated vertices and dominated
edges (both preserve the homotopy type of a clique complex), then compare Betti
numbers mod 2, mod 3 and mod P = 1000003.  A difference certifies torsion.

Evidence only: random families, bounded sizes.  Single-threaded, modest.
Usage: python3 relative_torsion_search.py SEED NCONFIGS [basic|dense]
"""
import itertools
import math
import random
import sys
import time

import numpy as np

P = 1000003
MAX_SIMPLICES = 3500


def graph_from_points(pts, r):
    n = len(pts)
    adj = [set() for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if math.dist(pts[i], pts[j]) <= r:
                adj[i].add(j)
                adj[j].add(i)
    return adj


def add_cone(adj, A):
    n = len(adj)
    new = [set(s) for s in adj] + [set(A)]
    for a in A:
        new[a].add(n)
    return new


def reduce_graph(adj):
    """Dominated-vertex and dominated-edge removal until stable."""
    adj = {v: set(s) for v, s in enumerate(adj)}
    changed = True
    while changed:
        changed = False
        for v in list(adj):
            Nv = adj[v] | {v}
            for u in adj[v]:
                if Nv <= (adj[u] | {u}):
                    for w in adj[v]:
                        adj[w].discard(v)
                    del adj[v]
                    changed = True
                    break
        for u in list(adj):
            if u not in adj:
                continue
            for v in list(adj[u]):
                if v < u:
                    continue
                common = (adj[u] & adj[v])
                Nuv = common | {u, v}
                for w in common:
                    if Nuv <= (adj[w] | {w}):
                        adj[u].discard(v)
                        adj[v].discard(u)
                        changed = True
                        break
    return adj


def cliques(adj):
    out = []
    verts = sorted(adj)

    def extend(cl, cand):
        out.append(cl)
        if len(out) > MAX_SIMPLICES:
            raise OverflowError
        for i, v in enumerate(cand):
            extend(cl + (v,), [w for w in cand[i + 1:] if w in adj[v]])

    for i, v in enumerate(verts):
        extend((v,), [w for w in verts[i + 1:] if w in adj[v]])
    return out


def rank_mod2(rows):
    basis = {}
    rank = 0
    for x in rows:
        while x:
            h = x.bit_length() - 1
            if h in basis:
                x ^= basis[h]
            else:
                basis[h] = x
                rank += 1
                break
    return rank


def rank_modp(M, p):
    M = M.copy() % p
    m, n = M.shape
    rank = 0
    col = 0
    for col in range(n):
        if rank == m:
            break
        piv = np.nonzero(M[rank:, col])[0]
        if len(piv) == 0:
            continue
        pr = rank + piv[0]
        if pr != rank:
            M[[rank, pr]] = M[[pr, rank]]
        inv = pow(int(M[rank, col]), p - 2, p)
        M[rank] = (M[rank] * inv) % p
        nz = np.nonzero(M[:, col])[0]
        nz = nz[nz != rank]
        if len(nz):
            M[nz] = (M[nz] - np.outer(M[nz, col], M[rank])) % p
        rank += 1
    return rank


def betti(adj):
    cl = cliques(adj)
    by_dim = {}
    for c in cl:
        by_dim.setdefault(len(c) - 1, []).append(c)
    top = max(by_dim) if by_dim else -1
    index = {d: {c: i for i, c in enumerate(by_dim[d])} for d in by_dim}
    ranks = {2: {}, 3: {}, P: {}}
    for d in range(1, top + 1):
        rows_bits = []
        mat = np.zeros((len(by_dim[d]), len(by_dim[d - 1])), dtype=np.int64)
        for i, c in enumerate(by_dim[d]):
            bits = 0
            for k in range(len(c)):
                face = c[:k] + c[k + 1:]
                j = index[d - 1][face]
                bits |= 1 << j
                mat[i, j] = 1 if k % 2 == 0 else -1
            rows_bits.append(bits)
        ranks[2][d] = rank_mod2(rows_bits)
        ranks[3][d] = rank_modp(mat, 3)
        ranks[P][d] = rank_modp(mat, P)
    res = {}
    for p in (2, 3, P):
        b = []
        for d in range(top + 1):
            b.append(len(by_dim[d]) - ranks[p].get(d, 0) - ranks[p].get(d + 1, 0))
        res[p] = b
    return res, len(cl)


def hexagon(cx, cy, rho=1.0, phase=0.0):
    return [(cx + rho * math.cos(phase + k * math.pi / 3), cy + rho * math.sin(phase + k * math.pi / 3)) for k in range(6)]


def midpoint_scales(pts, lo, hi, k, rng):
    ds = sorted({round(math.dist(p, q), 9) for p, q in itertools.combinations(pts, 2)})
    mids = [(a + b) / 2 for a, b in zip(ds, ds[1:]) if lo <= (a + b) / 2 <= hi and b - a > 1e-6]
    rng.shuffle(mids)
    return mids[:k]


def dense_configs(rng, count):
    """Denser families (mode 'dense'): a hexagon with 8-16 random points, and a
    chain-like pair of hexagons A, A + (D, 0) with 6-14 points in the strip."""
    made = 0
    while made < count:
        fam = rng.choice(["hexdense", "chain"])
        if fam == "hexdense":
            pts = hexagon(0, 0, 1, 0)
            k = rng.randint(8, 16)
            pts += [(rng.uniform(-2.5, 2.5), rng.uniform(-2.5, 2.5)) for _ in range(k)]
            for r in midpoint_scales(pts, 1.74, 1.99, 2, rng):
                yield fam, pts, r, list(range(6))
                made += 1
        else:
            D = rng.uniform(2.2, 4.5)
            ph = rng.uniform(0, 1)
            pts = hexagon(0, 0, 1, ph) + hexagon(D, 0, 1, ph)
            k = rng.randint(6, 14)
            pts += [(rng.uniform(-1.5, D + 1.5), rng.uniform(-1.8, 1.8)) for _ in range(k)]
            r = rng.uniform(1.74, 1.99)
            yield fam, pts, r, list(range(6))
            yield fam + "-both", pts, r, list(range(12))
            made += 2


def configs(rng, count):
    """Yield (family, points, r, A)."""
    made = 0
    while made < count:
        fam = rng.choice(["twohex", "hexcloud", "disk", "halfplane"])
        if fam == "twohex":
            D = rng.uniform(2.2, 4.2)
            pts = hexagon(0, 0, 1, rng.uniform(0, 1)) + hexagon(D, rng.uniform(-0.5, 0.5), 1, rng.uniform(0, 1))
            k = rng.randint(2, 7)
            pts += [(rng.uniform(-1.2, D + 1.2), rng.uniform(-1.6, 1.6)) for _ in range(k)]
            r = rng.uniform(1.74, 1.99)
            A = list(range(6))
            yield fam, pts, r, A
            yield fam + "-both", pts, r, list(range(12))
            made += 2
        elif fam == "hexcloud":
            pts = hexagon(0, 0, 1, 0)
            k = rng.randint(3, 8)
            pts += [(rng.uniform(-2.2, 2.2), rng.uniform(-2.2, 2.2)) for _ in range(k)]
            for r in midpoint_scales(pts, 1.74, 1.99, 3, rng):
                yield fam, pts, r, list(range(6))
                made += 1
        elif fam == "disk":
            n = rng.randint(8, 13)
            pts = []
            while len(pts) < n:
                x, y = rng.uniform(-1, 1), rng.uniform(-1, 1)
                if x * x + y * y <= 1:
                    pts.append((x, y))
            for r in midpoint_scales(pts, 0.9, 1.95, 3, rng):
                m = rng.randint(2, 4)
                A = sorted(rng.sample(range(n), n - m))
                yield fam, pts, r, A
                made += 1
        else:
            n = rng.randint(9, 14)
            pts = [(rng.uniform(-1.5, 1.5), rng.uniform(-1.5, 1.5)) for _ in range(n)]
            th = rng.uniform(0, math.pi)
            c = (math.cos(th), math.sin(th))
            A = [i for i, q in enumerate(pts) if q[0] * c[0] + q[1] * c[1] < rng.uniform(-0.5, 0.5)]
            if 2 <= n - len(A) and len(A) >= 3:
                for r in midpoint_scales(pts, 1.0, 2.4, 2, rng):
                    yield fam, pts, r, A
                    made += 1


def calibrate():
    # regular hexagon at r = 1.9: octahedron, Betti [1,0,1]
    pts = hexagon(0, 0)
    res, _ = betti(reduce_graph(graph_from_points(pts, 1.9)))
    assert res[P][:3] == [1, 0, 1], res
    # relative to a 5-point subset (a cone): relative complex still S^2
    adj = add_cone(graph_from_points(pts, 1.9), list(range(5)))
    res, _ = betti(reduce_graph(adj))
    assert res[P][:3] == [1, 0, 1], res
    # relative to the full hexagon: the cone, contractible
    adj = add_cone(graph_from_points(pts, 1.9), list(range(6)))
    res, _ = betti(reduce_graph(adj))
    assert res[P] == [1], res
    # abstract 6-vertex RP^2 (flag? no -- use clique complex of its 1-skeleton plus
    # removal of missing triangles is not flag); instead test mod-2 detection on the
    # 3x3 torus-like Moebius strip boundary is skipped.  Direct rank test:
    M = np.array([[2]], dtype=np.int64)
    assert rank_mod2([0]) == 0 and rank_modp(M, 3) == 1 and rank_modp(M, P) == 1
    print("calibration ok", flush=True)


def main():
    global MAX_SIMPLICES
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    count = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    mode = sys.argv[3] if len(sys.argv) > 3 else "basic"
    rng = random.Random(seed)
    calibrate()
    if mode == "dense":
        MAX_SIMPLICES = 6000
        gen = dense_configs(rng, count)
    else:
        gen = configs(rng, count)
    t0 = time.time()
    stats = {}
    flagged = []
    skipped = 0
    for fam, pts, r, A in gen:
        adj = add_cone(graph_from_points(pts, r), A)
        red = reduce_graph(adj)
        try:
            res, ns = betti(red)
        except OverflowError:
            skipped += 1
            continue
        s = stats.setdefault(fam, [0, 0, 0])
        s[0] += 1
        if sum(res[P][1:]) > 0:
            s[1] += 1
        if res[2] != res[P] or res[3] != res[P]:
            s[2] += 1
            flagged.append((fam, pts, r, A, res))
            print("FLAG", fam, r, A, res, pts, flush=True)
    print("mode", mode, "seed", seed, "configs", count, "skipped(size)", skipped, "time %.1fs" % (time.time() - t0))
    for fam, (tot, nontriv, fl) in sorted(stats.items()):
        print("%-14s tested %5d  nontrivial-relative-homology %5d  torsion-flags %d" % (fam, tot, nontriv, fl))


if __name__ == "__main__":
    main()
