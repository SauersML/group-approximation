"""Cross-checks for the Jensen-Helly property of l^1 cube complexes of RAAGs.

For a finite convex subcomplex K of a RAAG Salvetti cover (dimension k) with
hyperplane coordinates c in [0,1]^H, and vertex centres z_i with offsets rho_i:

  s_X(T)   = min over points p of |K| of max_{i in T} (d(z_i,p) - rho_i)
  s_box(T) = the same minimum over the whole box [0,1]^H

Tests:
  (H)  s_X(all) == max over (k+1)-subsets T of s_X(T)   [Helly number k+1]
       and we count how often s_X(all) > max over k-subsets (teeth check).
  (E)  s_box(T) == s_X(T) for all T [the unfolding retraction: every box
       point can be moved into |K| without increasing any L_x].
  (U)  a minimiser of Phi = sum_x L_x over D = {c : L_x(c) <= L_x(w)}, with
       w the halfspace-mass vector of a random measure, satisfies (*): no
       pair of distinct hyperplanes charges an empty quadrant.
Usage: python3 jhelly.py seed R trials graphs
"""
import sys, random, itertools
import numpy as np
from scipy.optimize import linprog
from raagcube import RAAG, ball, hull_fast, Complex

GRAPHS = {
    "P4": (4, [(0, 1), (1, 2), (2, 3)]),
    "C5": (5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]),
    "K1*P4": (5, [(0, 1), (1, 2), (2, 3), (4, 0), (4, 1), (4, 2), (4, 3)]),
    "tri+pendant": (4, [(0, 1), (1, 2), (0, 2), (2, 3)]),
    "K4-path": (4, [(0, 1), (0, 2), (0, 3), (1, 2)]),
    "K2*P4": (6, [(0, 1), (1, 2), (2, 3)] + [(a, b) for a in (4, 5) for b in range(4)] + [(4, 5)]),
}


def aff(K, i):
    """L_x(c) = a . c + const for the vertex with index i."""
    cx = K.coord[i]
    a = np.array([-1.0 if (cx >> h) & 1 else 1.0 for h in range(K.nh)])
    return a, float(bin(cx).count("1"))


def minmax_over_cube(K, rows, f, m):
    free = [h for h in range(K.nh) if (m >> h) & 1]
    k = len(free)
    Aub = []
    bub = []
    for (a, const, rho) in rows:
        # a.c + const - rho <= s ; fixed coordinates contribute a_h * bit
        cst = const - rho + sum(a[h] * ((f >> h) & 1) for h in range(K.nh) if not (m >> h) & 1)
        Aub.append([a[h] for h in free] + [-1.0])
        bub.append(-cst)
    c = np.zeros(k + 1); c[-1] = 1.0
    res = linprog(c, A_ub=np.array(Aub), b_ub=np.array(bub),
                  bounds=[(0, 1)] * k + [(None, None)], method="highs")
    assert res.status == 0
    return res.fun


def s_X(K, cubes, rows):
    return min(minmax_over_cube(K, rows, f, m) for (f, m) in cubes)


def s_box(K, rows):
    n = K.nh
    Aub = [list(a) + [-1.0] for (a, const, rho) in rows]
    bub = [-(const - rho) for (a, const, rho) in rows]
    c = np.zeros(n + 1); c[-1] = 1.0
    res = linprog(c, A_ub=np.array(Aub), b_ub=np.array(bub),
                  bounds=[(0, 1)] * n + [(None, None)], method="highs")
    assert res.status == 0
    return res.fun


def empty_quadrants(K):
    nv = len(K.V)
    S = []
    for h in range(K.nh):
        one = 0
        for i in range(nv):
            if (K.coord[i] >> h) & 1:
                one |= 1 << i
        S.append((((1 << nv) - 1) & ~one, one))
    out = []
    for h in range(K.nh):
        for g in range(h + 1, K.nh):
            for al in (0, 1):
                for be in (0, 1):
                    if S[h][al] & S[g][be] == 0:
                        out.append((h, al, g, be))
    return out


def charge(c, h, al):
    return c[h] if al == 1 else 1.0 - c[h]


def test_unfold(K, rng, supp):
    nv = len(K.V)
    idx = rng.sample(range(nv), min(supp, nv))
    ws = [rng.randint(1, 5) for _ in idx]
    tot = sum(ws)
    w = np.zeros(K.nh)
    for i, wt in zip(idx, ws):
        for h in range(K.nh):
            if (K.coord[i] >> h) & 1:
                w[h] += wt / tot
    A = []
    b = []
    obj = np.zeros(K.nh)
    for i in range(nv):
        a, const = aff(K, i)
        A.append(a)
        b.append(a @ w)
        obj += a
    res = linprog(obj, A_ub=np.array(A), b_ub=np.array(b) + 1e-12,
                  bounds=[(0, 1)] * K.nh, method="highs")
    assert res.status == 0
    c = res.x
    worst = 0.0
    for (h, al, g, be) in empty_quadrants(K):
        worst = max(worst, min(charge(c, h, al), charge(c, g, be)))
    return worst


def run(name, R, trials, rng):
    n, edges = GRAPHS[name]
    G = RAAG(n, edges)
    k = G.dim
    B = sorted(ball(G, R))
    stats = dict(trials=0, helly_fail=0, teeth=0, box_mismatch=0, unfold_worst=0.0, maxV=0)
    for tr in range(trials):
        m = rng.choice([k + 2, k + 3])
        Z = rng.sample(B, m)
        extra = rng.sample(B, rng.randint(0, 2))
        K = Complex(G, hull_fast(G, list(Z) + extra))
        assert K.check_isometric(100, rng)
        stats["maxV"] = max(stats["maxV"], len(K.V))
        cubes = K.cubes()
        rows_all = []
        for z in Z:
            a, const = aff(K, K.idx[z])
            rho = rng.choice([0, 0.5, 1, 1.5, 2, 2.5, 3]) if rng.random() < 0.7 else rng.uniform(0, 3)
            rows_all.append((a, const, rho))
        full = s_X(K, cubes, rows_all)
        fb = s_box(K, rows_all)
        if abs(full - fb) > 1e-7:
            stats["box_mismatch"] += 1
            print(name, "BOX MISMATCH", full, fb, Z)
        mk1 = max(s_X(K, cubes, [rows_all[i] for i in T]) for T in itertools.combinations(range(m), k + 1))
        mk = max(s_X(K, cubes, [rows_all[i] for i in T]) for T in itertools.combinations(range(m), k))
        if full > mk1 + 1e-7:
            stats["helly_fail"] += 1
            print(name, "HELLY FAIL", full, mk1, Z, [r[2] for r in rows_all])
        if full > mk + 1e-7:
            stats["teeth"] += 1
        stats["unfold_worst"] = max(stats["unfold_worst"], test_unfold(K, rng, rng.randint(2, 6)))
        stats["trials"] += 1
    print(name, "k=%d R=%d" % (k, R), stats)
    sys.stdout.flush()


if __name__ == "__main__":
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    R = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    trials = int(sys.argv[3]) if len(sys.argv) > 3 else 10
    names = sys.argv[4].split(",") if len(sys.argv) > 4 else ["P4", "K1*P4"]
    rng = random.Random(seed)
    for nm in names:
        run(nm, R, trials, rng)
