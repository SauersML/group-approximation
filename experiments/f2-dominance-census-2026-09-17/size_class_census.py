#!/usr/bin/env python3
"""Subgroup-dominance constant C(S) by column generation with exact pricing, plus exact
size-class census via the span reduction.

C(S) = min over distributions p on subgroups H, |H| = s, of max_{a != 0} Pr_p[a not in H] / d_S(a),
d_S(a) = |S \\ (S+a)| / s.  (Notation of research/f2-cayley-subgroup-sets-are-constant-factor-optimal.md.)

Span reduction (proved in research/f2-cayley-dominance-size-eight-class-proof.md (Step 1)):
C(S) computed in F_2^k equals C(S) computed in V = span(S - S), and dim V <= s - 1.
So sup_{|S| = s, all k} C(S) is a finite computation: S contains {0, e_1, ..., e_r}
(r = dim V) plus s - 1 - r further points of F_2^r.

Certificates: every reported value comes with an exact rational upper bound (a rationalised
primal p, max ratio checked in Fractions) and an exact rational lower bound (a rationalised
dual weight w, min over ALL subgroups of sum_a w_a 1[a not in H] / sum_a w_a d(a), in Fractions).

Usage:
  size_class_census.py census s            exact sup over all |S| = s  (s = 8 feasible)
  size_class_census.py search k s iters seed
  size_class_census.py ball s              radius-one ball {0, e_1..e_(s-1)} in F_2^(s-1)
"""
import itertools, json, random, sys
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog

_SUBS = {}


def subspaces(r, j):
    """All j-dim subspaces of F_2^r as an int array (#subspaces, 2^j) of elements (row 0 is 0)."""
    key = (r, j)
    if key in _SUBS:
        return _SUBS[key]
    blocks = []
    coeff = np.array(list(itertools.product([0, 1], repeat=j)), dtype=np.int64)  # 2^j x j
    for piv in itertools.combinations(range(r), j):
        piv = sorted(piv, reverse=True)
        pivset = set(piv)
        free = [[q for q in range(p) if q not in pivset] for p in piv]
        F = sum(len(f) for f in free)
        idx = np.arange(1 << F, dtype=np.int64)
        rows = []
        off = 0
        for p, f in zip(piv, free):
            v = np.full(1 << F, 1 << p, dtype=np.int64)
            for t, q in enumerate(f):
                v |= ((idx >> (off + t)) & 1) << q
            off += len(f)
            rows.append(v)
        B = np.stack(rows, axis=1)  # N x j
        elems = np.zeros((B.shape[0], 1 << j), dtype=np.int64)
        for ci, cvec in enumerate(coeff):
            acc = np.zeros(B.shape[0], dtype=np.int64)
            for t in range(j):
                if cvec[t]:
                    acc ^= B[:, t]
            elems[:, ci] = acc
        blocks.append(elems)
    out = np.concatenate(blocks, axis=0)
    _SUBS[key] = out
    return out


def d_vector(k, S):
    N = 1 << k
    ind = np.zeros(N, dtype=bool)
    ind[list(S)] = True
    Sa = np.array(sorted(S), dtype=np.int64)
    s = len(S)
    d = np.empty(N)
    d[0] = 0.0
    for a in range(1, N):
        d[a] = 1.0 - ind[Sa ^ a].sum() / s
    return d


def C_value(k, S, max_rounds=400, tol=1e-10):
    """Column generation. Returns (C, p dict H_index->prob, w vector on a, subspace array)."""
    s = len(S)
    j = s.bit_length() - 1
    assert 1 << j == s
    Hs = subspaces(k, j)
    N = 1 << k
    d = d_vector(k, S)
    act = [a for a in range(1, N) if d[a] < 1 - 1e-12]  # d = 1 rows hold automatically when t >= 1
    if not act:
        return 1.0, {}, np.zeros(N), Hs
    pos = {a: i for i, a in enumerate(act)}
    member = np.zeros((Hs.shape[0], N), dtype=bool) if Hs.shape[0] * N <= 4e8 else None
    rng = np.random.default_rng(0)
    cols = list(rng.choice(Hs.shape[0], size=min(200, Hs.shape[0]), replace=False))

    def miss_col(h):
        m = np.ones(len(act))
        for x in Hs[h]:
            if x in pos:
                m[pos[x]] = 0.0
        return m

    colvec = {h: miss_col(h) for h in cols}
    dact = d[act]
    for _ in range(max_rounds):
        nH = len(cols)
        A = np.zeros((len(act), nH + 1))
        for i, h in enumerate(cols):
            A[:, i] = colvec[h]
        A[:, -1] = -dact
        c = np.zeros(nH + 1); c[-1] = 1
        Aeq = np.zeros((1, nH + 1)); Aeq[0, :nH] = 1
        res = linprog(c, A_ub=A, b_ub=np.zeros(len(act)), A_eq=Aeq, b_eq=[1],
                      bounds=[(0, None)] * nH + [(1, None)], method="highs")
        assert res.status == 0, res.message
        y = -res.ineqlin.marginals          # >= 0
        mu = res.eqlin.marginals[0]
        # pricing: minimise sum_a y_a miss(H,a) = Y - y(H); want < mu
        yfull = np.zeros(N)
        yfull[act] = y
        gain = yfull[Hs].sum(axis=1)       # y(H)
        order = np.argsort(-gain)
        Y = y.sum()
        new = [int(h) for h in order[:50] if Y - gain[h] < mu - tol and int(h) not in colvec]
        if not new:
            break
        for h in new:
            colvec[h] = miss_col(h)
            cols.append(h)
    p = {cols[i]: res.x[i] for i in range(len(cols)) if res.x[i] > 1e-12}
    w = np.zeros(N)
    w[act] = y
    return float(res.fun), p, w, Hs


def certify(k, S, p, w, Hs, den=10 ** 6):
    """Exact rational bounds lower <= C(S) <= upper."""
    s = len(S)
    Sset = set(S)
    N = 1 << k
    dF = [Fraction(0)] + [Fraction(sum(1 for v in S if v ^ a not in Sset), s) for a in range(1, N)]
    # upper: rationalise p
    upper = None
    inHs = {h: set(int(x) for x in Hs[h]) for h in p}
    for D in (12, 24, 48, 100, 420, 1000, 10 ** 4, 10 ** 6):
        pr = {h: Fraction(q).limit_denominator(D) for h, q in p.items()}
        pr = {h: q for h, q in pr.items() if q > 0}
        tot = sum(pr.values())
        pr = {h: q / tot for h, q in pr.items()}
        missF = [Fraction(0)] * N
        for h, q in pr.items():
            for a in range(1, N):
                if a not in inHs[h]:
                    missF[a] += q
        u = max([Fraction(1)] + [missF[a] / dF[a] for a in range(1, N) if dF[a] > 0])
        upper = u if upper is None else min(upper, u)
    # lower: rationalise w, exact min over all H
    wr = [Fraction(float(x)).limit_denominator(1000) if x > 1e-12 else Fraction(0) for x in w]
    L = 1
    for x in wr:
        L = L * x.denominator // __import__("math").gcd(L, x.denominator)
    den = L
    denom = sum(wr[a] * dF[a] for a in range(1, N))
    lower = Fraction(1)
    if denom > 0:
        wi = np.array([int(x * den) for x in wr], dtype=object).astype(np.int64)  # exact integers (den-scaled)
        Wtot = int(wi.sum())
        inside = wi[Hs].sum(axis=1)                               # exact int64 sums
        best_miss = Fraction(Wtot - int(inside.max()), den)
        lower = max(lower, best_miss / denom)
    return lower, upper


def span_dim(S):
    basis = []
    for v in S:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
    return len(basis)


def census(s):
    """sup C(S) over all |S| = s, every k, via span reduction + S >= {0, e_1..e_r}."""
    j = s.bit_length() - 1
    results = []
    for r in range(j, s):
        base = [0] + [1 << i for i in range(r)]
        pool = [x for x in range(1, 1 << r) if x & (x - 1)]  # weight >= 2
        extra = s - 1 - r
        seen = set()
        for comb in itertools.combinations(pool, extra):
            # cheap symmetry cut: canonical under coordinate permutations (sorted weight profile key)
            S = tuple(sorted(base + list(comb)))
            key = canon_perm(S, r)
            if key in seen:
                continue
            seen.add(key)
            C, p, w, Hs = C_value(r, S)
            lo, up = certify(r, S, p, w, Hs)
            results.append((float(up), r, S, str(lo), str(up)))
        print(f"r={r}: {len(seen)} classes (up to coordinate permutation)", flush=True)
    results.sort(reverse=True)
    return results


def canon_perm(S, r):
    best = None
    for perm in itertools.permutations(range(r)) if r <= 6 else [tuple(range(r))]:
        img = tuple(sorted(sum(((x >> i) & 1) << perm[i] for i in range(r)) for x in S))
        if best is None or img < best:
            best = img
    return best


def search(k, s, iters, seed):
    rng = random.Random(seed)
    N = 1 << k
    S = [0] + rng.sample(range(1, N), s - 1)
    if seed < 0:  # start from {0, e_1..e_k} plus random extra points (ball-like start)
        base = [0] + [1 << i for i in range(k)]
        S = base + rng.sample([x for x in range(1, N) if x & (x - 1)], s - len(base))
    C, p, w, Hs = C_value(k, S)
    for it in range(iters):
        S2 = S[:]
        S2[rng.randrange(1, s)] = rng.randrange(1, N)
        if len(set(S2)) < s:
            continue
        C2, p2, w2, _ = C_value(k, S2)
        if C2 >= C - 1e-12:
            if C2 > C + 1e-9:
                print(f"it {it}: C = {C2:.6f}  S = {sorted(S2)}", flush=True)
            S, C, p, w = S2, C2, p2, w2
    lo, up = certify(k, S, p, w, Hs)
    return C, sorted(S), str(lo), str(up)


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "census":
        s = int(sys.argv[2])
        res = census(s)
        for row in res:
            print(json.dumps(dict(C_upper_float=row[0], r=row[1], S=row[2], lower=row[3], upper=row[4])))
        print(json.dumps(dict(s=s, classes=len(res), sup_upper=res[0][4], sup_lower=max(Fraction(x[3]) for x in res).__str__())))
    elif mode == "search":
        k, s, iters, seed = map(int, sys.argv[2:6])
        C, S, lo, up = search(k, s, iters, seed)
        print(json.dumps(dict(k=k, s=s, C=C, S=S, lower=lo, upper=up)))
    elif mode == "ball":
        s = int(sys.argv[2])
        k = s - 1
        S = [0] + [1 << i for i in range(k)]
        C, p, w, Hs = C_value(k, S)
        lo, up = certify(k, S, p, w, Hs)
        print(json.dumps(dict(s=s, k=k, C=C, lower=str(lo), upper=str(up))))
