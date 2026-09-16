"""Helly number of l^1-balls through split systems.

For vertices z_0..z_{m-1} of a finite CAT(0) cube complex X, the hyperplanes
separating centres induce splits S of {0..m-1} with multiplicities n_S.  The
minimum over the box [0,1]^H of max_{i in T} (d(z_i,c) - rho_i) is

  s(T) = min_{c in [0,1]^splits} max_{i in T} sum_S n_S |[i in S] - c_S| - rho_i,

and by the unfolding retraction (tested directly in jhelly.py, test E) the
same minimum is attained on |X|.  Every split system with multiplicities is
realised by points of a CAT(0) cube complex (Sageev-Roller cubulation of the
split poc set, copies nested), of dimension kappa = the largest set of
pairwise incompatible splits.  So Helly number kappa+1 for balls in |X| is the
statement  s(all) <= max over (kappa+1)-subsets T of s(T)  for every rho.
We hill-climb rho to maximise the gap.  Teeth: the same search with kappa
subsets finds positive gaps.
Usage: python3 jhelly_splits.py seed m systems steps
"""
import sys, random, itertools
import numpy as np
from scipy.optimize import linprog


def all_splits(m):
    out = []
    for r in range(1, m):
        for S in itertools.combinations(range(m), r):
            if 0 in S:
                out.append(frozenset(S))
    return out


def incompatible(S, Sp, m):
    U = frozenset(range(m))
    return all(len(X & Y) > 0 for X in (S, U - S) for Y in (Sp, U - Sp))


def max_clique(splits, m):
    best = 0
    n = len(splits)
    adj = [[incompatible(splits[a], splits[b], m) for b in range(n)] for a in range(n)]
    def rec(cands, size):
        nonlocal best
        best = max(best, size)
        for idx, v in enumerate(cands):
            rec([u for u in cands[idx + 1:] if adj[v][u]], size + 1)
    rec(list(range(n)), 0)
    return best


def s_val(system, T, rho):
    """system: list of (split, mult)."""
    ns = len(system)
    A = []
    b = []
    for i in T:
        row = []
        const = 0.0
        for (S, n) in system:
            if i in S:
                row.append(-n); const += n
            else:
                row.append(n)
        row.append(-1.0)
        A.append(row)
        b.append(rho[i] - const)
    c = np.zeros(ns + 1); c[-1] = 1.0
    res = linprog(c, A_ub=np.array(A, dtype=float), b_ub=np.array(b),
                  bounds=[(0, 1)] * ns + [(None, None)], method="highs")
    assert res.status == 0
    return res.fun


def gap(system, m, j, rho):
    full = s_val(system, range(m), rho)
    return full - max(s_val(system, T, rho) for T in itertools.combinations(range(m), j))


def climb(system, m, j, steps, rng):
    rho = [rng.uniform(0, 4) for _ in range(m)]
    best = gap(system, m, j, rho)
    for st in range(steps):
        i = rng.randrange(m)
        new = list(rho); new[i] += rng.choice([0.5, 0.25, 0.125, 0.05]) * rng.choice([-1, 1])
        g = gap(system, m, j, new)
        if g >= best - 1e-12:
            rho, best = new, g
    return best, rho


if __name__ == "__main__":
    seed = int(sys.argv[1]); m = int(sys.argv[2]); systems = int(sys.argv[3]); steps = int(sys.argv[4])
    rng = random.Random(seed)
    splits = all_splits(m)
    # sanity: the R^3 example (Z^3 coordinates of 4 points) must show gap > 0 for j = 3
    if m == 4:
        pts = [(0, -1, -1), (-2, 0, -2), (-1, 1, 0), (1, 1, -2)]
        mult = {}
        for coord in range(3):
            vals = sorted(set(p[coord] for p in pts))
            for lo, hi in zip(vals, vals[1:]):
                S = frozenset(i for i, p in enumerate(pts) if p[coord] <= lo)
                if 0 not in S:
                    S = frozenset(range(m)) - S
                mult[S] = mult.get(S, 0) + (hi - lo)
        sysR3 = list(mult.items())
        print("R^3 example: kappa", max_clique([S for S, n in sysR3], m),
              "gap_3", gap(sysR3, m, 3, [2.5, 2.5, 2.5, 2.0]))
    stats = {}
    for sy in range(systems):
        if rng.random() < 0.5:
            present = [S for S in splits if rng.random() < rng.choice([0.3, 0.5, 0.8])]
        else:
            present = rng.sample(splits, rng.randint(2, min(len(splits), 2 * m)))
        if not present:
            continue
        system = [(S, rng.choice([1, 1, 2, 3])) for S in present]
        kap = max_clique(present, m)
        if kap + 1 >= m:
            continue  # nothing to test: Helly number kappa+1 >= m is automatic
        g1, r1 = climb(system, m, kap + 1, steps, rng)
        g0, r0 = climb(system, m, kap, steps, rng) if kap >= 1 else (0.0, None)
        st = stats.setdefault(kap, [0, 0, 0, -1e9])
        st[0] += 1
        if g1 > 1e-7:
            st[1] += 1
            print("HELLY kappa+1 FAIL", kap, g1, [(sorted(S), n) for S, n in system], r1)
        if g0 > 1e-7:
            st[2] += 1
        st[3] = max(st[3], g1)
    for kap in sorted(stats):
        n, fail, teeth, mx = stats[kap]
        print("m=%d kappa=%d systems=%d fail(kappa+1)=%d teeth(kappa fails)=%d max gap(kappa+1)=%.3g" % (m, kap, n, fail, teeth, mx))
