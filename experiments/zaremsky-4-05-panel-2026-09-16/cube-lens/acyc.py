"""Direct check that nonempty intersections B_I of vertex-centred d_1-balls in |X| are acyclic
(independent of Lemma Rt).  B_I is the union of the convex pieces B_I cap Q over maximal cubes Q;
pieces and their intersections are convex, so B_I is homotopy equivalent to the nerve of the
nonempty pieces.  We compute the nerve by LP feasibility and its reduced Betti numbers over GF(2).
Usage: python3 acyc.py seed trials [names]
"""
import sys, random, itertools
import numpy as np
from scipy.optimize import linprog
from graphs import zoo


def feasible(G, cubes, Z, rho):
    """Is B_I cap (intersection of the given maximal cubes) nonempty?"""
    m = G.m
    lo = np.zeros(m); hi = np.ones(m)
    for base, F in cubes:
        for h in range(m):
            if h not in F:
                lo[h] = max(lo[h], base[h]); hi[h] = min(hi[h], base[h])
    if (lo > hi + 1e-12).any():
        return False
    A, b = [], []
    for z, r in zip(Z, rho):
        a, const = G.Lcoef(z)
        A.append(a); b.append(r - const)
    res = linprog(np.zeros(m), A_ub=np.array(A), b_ub=np.array(b),
                  bounds=list(zip(lo, np.maximum(lo, hi))), method="highs")
    return res.status == 0


def rank_gf2(M):
    M = M.copy() % 2
    r = 0
    rows, cols = M.shape
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if M[i, c]:
                piv = i; break
        if piv is None:
            continue
        M[[r, piv]] = M[[piv, r]]
        for i in range(rows):
            if i != r and M[i, c]:
                M[i] ^= M[r]
        r += 1
        if r == rows:
            break
    return r


def reduced_betti(simplices):
    """simplices: set of frozensets (closed under subsets, nonempty)."""
    by_dim = {}
    for s in simplices:
        by_dim.setdefault(len(s) - 1, []).append(tuple(sorted(s)))
    maxd = max(by_dim)
    idx = {d: {s: i for i, s in enumerate(by_dim[d])} for d in by_dim}
    ranks = {}
    for d in range(1, maxd + 1):
        M = np.zeros((len(by_dim[d - 1]), len(by_dim[d])), dtype=np.uint8)
        for j, s in enumerate(by_dim[d]):
            for t in itertools.combinations(s, d):
                M[idx[d - 1][t], j] = 1
        ranks[d] = rank_gf2(M)
    betti = []
    for d in range(0, maxd + 1):
        nd = len(by_dim[d])
        rk_out = ranks.get(d, 0)  # rank of boundary d -> d-1
        rk_in = ranks.get(d + 1, 0)
        b = nd - rk_out - rk_in
        if d == 0:
            b -= 1  # reduced
        betti.append(b)
    return betti


def nerve(G, Z, rho, maxsimp=10):
    verts = [i for i, Q in enumerate(G.maxcubes) if feasible(G, [Q], Z, rho)]
    simp = set(frozenset([v]) for v in verts)
    frontier = [frozenset([v]) for v in verts]
    while frontier:
        new = []
        for s in frontier:
            for v in verts:
                if v > max(s):
                    t = s | {v}
                    if len(t) > maxsimp:
                        continue
                    if all((t - {u}) in simp for u in t) and feasible(G, [G.maxcubes[i] for i in t], Z, rho):
                        if t not in simp:
                            simp.add(t); new.append(t)
        frontier = new
    return verts, simp


if __name__ == "__main__":
    seed = int(sys.argv[1]); trials = int(sys.argv[2])
    names = sys.argv[3].split(",") if len(sys.argv) > 3 else None
    rng = random.Random(seed)
    for G in zoo(seed):
        if names and G.name not in names:
            continue
        bad = 0; nonempty = 0; maxpieces = 0; nontriv = 0
        for _ in range(trials):
            cn = rng.randint(1, min(4, G.n))
            Z = rng.sample(range(G.n), cn)
            dm = G.D.max()
            rho = [rng.choice([rng.uniform(0, dm), rng.randint(0, dm), rng.randint(0, 2 * dm) / 2]) for _ in Z]
            verts, simp = nerve(G, Z, rho)
            if not verts:
                continue
            nonempty += 1
            maxpieces = max(maxpieces, len(verts))
            if len(verts) > 1:
                nontriv += 1
            betti = reduced_betti(simp)
            if any(b != 0 for b in betti):
                bad += 1
                print("  NONACYCLIC", G.name, Z, rho, betti, flush=True)
        print(G.name, "k", G.k, "maxcubes", len(G.maxcubes), "nonempty", nonempty, "multi-piece", nontriv,
              "maxpieces", maxpieces, "nonacyclic", bad, flush=True)
