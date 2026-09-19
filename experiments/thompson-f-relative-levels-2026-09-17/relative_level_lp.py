"""Exact LP for relatively separated (absolutely overlapping) size laws.

Claim: research/thompson-f-tree-size-observations-have-zero-defect.md (Attempts, w17-f-follow);
scouting for research/thompson-f-tower-size-laws-have-zero-defect.md (few levels fail; the
tower law, one separated random scale per leaf, succeeds).

Model.  Each non-extreme depth-d leaf v gets a relative level l_v in {1..L} and a weight c_v.
Sizes are X_v = Lam * Gam^(l_v - 1) * c_v with log Lam uniform over a huge range and
log log Gam uniform over a huge range (so no deterministic threshold separates levels).
For a word s with middle pieces p_1..p_(w-1), the TV-limit observation of the middle sizes is

  Obs_s = ( the ordered set partition of positions by top level L_j = max_{v<=p_j} l_v,
            within each block the projective vector of C_j = sum of c_v at level L_j,
            and, when there are >= 3 blocks, the ratios of the level gaps ).

Two configurations with equal Obs_s give middle-size laws at TV distance -> 0, and different
Obs_s are distinguishable, so a law on configurations is a zero-defect law for Psi_mid iff the
law of Obs_s is the same for every word s.  We solve the LP  min sum |violation|  over laws on
all configurations in {1..L}^n x W^n.

Usage: python3 relative_level_lp.py m d L w1,w2,...
"""
import itertools
import os
import sys
from fractions import Fraction

import numpy as np
import scipy.sparse as sp
from scipy.optimize import linprog

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "thompson-f-size-observation-2026-09-17"))
from level_search import monomial_set  # noqa: E402
from equal_middle_lp import antichain, leaves  # noqa: E402


def setup(m, d):
    S = monomial_set(m, d)
    LV = leaves(m, d)
    mids = [antichain(m, w)[1:-1] for w in S]

    def lset(node):
        a, q = node
        return tuple(i for i, (b, r) in enumerate(LV) if b == a and r.startswith(q))

    return S, LV, [[lset(x) for x in p] for p in mids]


def obs(pieces, lev, wt):
    tops = []
    for P in pieces:
        L = max(lev[i] for i in P)
        C = sum(wt[i] for i in P if lev[i] == L)
        tops.append((L, C))
    levels = sorted(set(t[0] for t in tops))
    blocks = []
    for L in levels:
        idx = tuple(j for j, t in enumerate(tops) if t[0] == L)
        tot = sum(tops[j][1] for j in idx)
        blocks.append((idx, tuple(Fraction(tops[j][1], tot) for j in idx)))
    gaps = ()
    if len(levels) >= 3:
        g = [levels[i + 1] - levels[i] for i in range(len(levels) - 1)]
        gaps = tuple(Fraction(x, g[0]) for x in g)
    return (tuple(blocks), gaps)


def solve(m, d, Lmax, W, verbose=True):
    S, LV, L = setup(m, d)
    n = len(LV)
    configs = []
    for lev in itertools.product(range(1, Lmax + 1), repeat=n):
        if min(lev) != 1:  # relative levels: normalise the minimum
            continue
        for wt in itertools.product(W, repeat=n):
            configs.append((lev, wt))
    N = len(configs)
    keys = {}
    rows, cols = [], []
    ob0 = [obs(L[0], *c) for c in configs]
    for s in range(1, len(S)):
        for k, c in enumerate(configs):
            o = obs(L[s], *c)
            if o == ob0[k]:
                continue
            for oo, sign in ((o, 1.0), (ob0[k], -1.0)):
                key = (s, oo)
                if key not in keys:
                    keys[key] = len(keys)
                rows.append(keys[key])
                cols.append((k, sign))
    R = len(keys)
    A = sp.csr_matrix(([c[1] for c in cols], (rows, [c[0] for c in cols])), shape=(R, N))
    # variables: p (N), u+ (R), u- (R)
    Aeq = sp.hstack([A, -sp.eye(R), sp.eye(R)])
    Aeq = sp.vstack([Aeq, sp.hstack([sp.csr_matrix(np.ones((1, N))), sp.csr_matrix((1, 2 * R))])])
    beq = np.zeros(R + 1)
    beq[-1] = 1.0
    cost = np.concatenate([np.zeros(N), np.ones(2 * R)])
    res = linprog(cost, A_eq=Aeq.tocsc(), b_eq=beq, bounds=(0, None), method="highs")
    p = res.x[:N]
    if verbose:
        print(f"(m,d)=({m},{d}) L={Lmax} W={W}: configs={N} constraints={R} min violation={res.fun:.6g}")
    return res.fun, configs, p, S, L


if __name__ == "__main__":
    m, d, Lmax = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    W = tuple(int(x) for x in sys.argv[4].split(",")) if len(sys.argv) > 4 else (1,)
    val, configs, p, S, L = solve(m, d, Lmax, W)
    supp = [(p[k], configs[k]) for k in np.argsort(-p)[:12] if p[k] > 1e-9]
    for q, c in supp:
        print(f"  p={q:.4f} levels={c[0]} weights={c[1]}")
