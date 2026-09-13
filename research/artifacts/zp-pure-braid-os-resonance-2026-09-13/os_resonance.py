#!/usr/bin/env python3
"""Aomoto-complex ranks for the Orlik-Solomon algebra of the braid arrangement A_{n-1} (P_n).

Basis: NBC monomials e_{i_1 j_1} ... e_{i_k j_k} with distinct tops j_1 < ... < j_k and i_s < j_s.
Reduction: e_{ik} e_{jk} = e_{ij} e_{jk} - e_{ij} e_{ik} for i < j < k (Arnold relation).
All linear algebra is over F_p with p = 2^31 - 1 at random points (generic-point test).
Usage: python3.11 os_resonance.py <n> [scan]
"""
import sys, random, itertools
from functools import lru_cache

P = 2147483647
n = int(sys.argv[1]) if len(sys.argv) > 1 else 5
SCAN = len(sys.argv) > 2 and sys.argv[2] == "scan"
EDGES = [(i, j) for j in range(2, n + 1) for i in range(1, j)]
EIDX = {e: t for t, e in enumerate(EDGES)}
KEY = lambda e: (e[1], e[0])

def sort_sign(lst):
    lst = list(lst); s = 1
    for a in range(len(lst)):
        for b in range(len(lst) - 1 - a):
            if KEY(lst[b]) > KEY(lst[b + 1]):
                lst[b], lst[b + 1] = lst[b + 1], lst[b]; s = -s
    return tuple(lst), s

@lru_cache(maxsize=None)
def reduce(mono):
    """mono: tuple of edges (exterior product in that order) -> dict NBC tuple -> coefficient (int)."""
    if len(set(mono)) < len(mono):
        return {}
    srt, s = sort_sign(mono)
    for t in range(len(srt) - 1):
        (i, k), (j, k2) = srt[t], srt[t + 1]
        if k == k2:  # i < j < k
            pre, suf = srt[:t], srt[t + 2:]
            out = {}
            for coef, pair in ((1, ((i, j), (j, k))), (-1, ((i, j), (i, k)))):
                for m, c in reduce(pre + pair + suf).items():
                    out[m] = out.get(m, 0) + s * coef * c
            return {m: c for m, c in out.items() if c != 0}
    return {srt: s}

def nbc_basis(k):
    res = []
    for tops in itertools.combinations(range(2, n + 1), k):
        for lows in itertools.product(*[range(1, j) for j in tops]):
            res.append(tuple(zip(lows, tops)))
    return res

BASIS = [nbc_basis(k) for k in range(n)]
BIDX = [{m: t for t, m in enumerate(B)} for B in BASIS]
# table[k][e] = list of (row index in degree k+1, column index in degree k, coefficient)
TABLE = []
for k in range(n - 1):
    tk = []
    for e in EDGES:
        ent = []
        for col, m in enumerate(BASIS[k]):
            for mm, c in reduce((e,) + m).items():
                ent.append((BIDX[k + 1][mm], col, c % P))
        tk.append(ent)
    TABLE.append(tk)

def rank_mod(rows, ncols):
    M = [r[:] for r in rows]; rk = 0; col = 0
    nr = len(M)
    while rk < nr and col < ncols:
        piv = None
        for r in range(rk, nr):
            if M[r][col] % P:
                piv = r; break
        if piv is None:
            col += 1; continue
        M[rk], M[piv] = M[piv], M[rk]
        inv = pow(M[rk][col], P - 2, P)
        M[rk] = [(x * inv) % P for x in M[rk]]
        for r in range(nr):
            if r != rk and M[r][col]:
                f = M[r][col]; M[r] = [(x - f * y) % P for x, y in zip(M[r], M[rk])]
        rk += 1; col += 1
    return rk

def aomoto_dims(a, upto=None):
    """a: list of coefficients indexed like EDGES. Returns [dim H^k] for k = 0..upto (default n-1)."""
    if upto is None:
        upto = n - 1
    ranks = []
    for k in range(min(n - 1, upto + 1)):
        rows = [[0] * len(BASIS[k]) for _ in BASIS[k + 1]]
        for t, e in enumerate(EDGES):
            if a[t] % P:
                for (r, c, v) in TABLE[k][t]:
                    rows[r][c] = (rows[r][c] + a[t] * v) % P
        ranks.append(rank_mod(rows, len(BASIS[k])))
    dims = []
    for k in range(min(n, upto + 1)):
        rin = ranks[k - 1] if k >= 1 else 0
        rout = ranks[k] if k < n - 1 else 0
        dims.append(len(BASIS[k]) - rin - rout)
    return dims

def nullspace_point(constraints):
    """Random point of {a : sum_e c_e a_e = 0 for each constraint vector c} over F_p."""
    N = len(EDGES)
    rows = [list(c) for c in constraints]
    # row reduce
    M = [r[:] for r in rows]; pivcols = []; rk = 0
    for col in range(N):
        piv = next((r for r in range(rk, len(M)) if M[r][col] % P), None)
        if piv is None: continue
        M[rk], M[piv] = M[piv], M[rk]
        inv = pow(M[rk][col], P - 2, P); M[rk] = [(x * inv) % P for x in M[rk]]
        for r in range(len(M)):
            if r != rk and M[r][col]:
                f = M[r][col]; M[r] = [(x - f * y) % P for x, y in zip(M[r], M[rk])]
        pivcols.append(col); rk += 1
    free = [c for c in range(N) if c not in pivcols]
    a = [0] * N
    for c in free: a[c] = random.randrange(1, P)
    for r, pc in enumerate(pivcols):
        a[pc] = (-sum(M[r][c] * a[c] for c in free)) % P
    return a, len(free)

def S_vec(S):
    return [1 if (e[0] in S and e[1] in S) else 0 for e in EDGES]

def row_vec(k):  # sum_{j != k} a_{kj}
    return [1 if k in e else 0 for e in EDGES]

if __name__ == "__main__":
    random.seed(20260913)
    print("n =", n, "Betti", [len(B) for B in BASIS])
    ALL = set(range(1, n + 1))
    zs = S_vec(ALL)
    tests = {
        "generic": [],
        "generic zero-sum": [zs],
        "KMM P3-circle {1,2,3}": [S_vec({1, 2, 3})] + [[1 if e == f else 0 for f in EDGES] for e in EDGES if not (e[0] <= 3 and e[1] <= 3)],
    }
    for name, cons in tests.items():
        a, dim = nullspace_point(cons)
        print(f"{name:40s} dim={dim} H^*={aomoto_dims(a)}", flush=True)
    if n == 5:
        blk = lambda A: [S_vec(A)] + [[1 if f == e else 0 for f in EDGES] for e in EDGES if not (e[0] in A and e[1] in A)]
        cases = {
            "zero-sum on {1,2,3,4}": blk({1, 2, 3, 4}),
            "all row sums zero": [row_vec(k) for k in range(1, 6)],
            "P4-circle{1234}+P3-circle{345}": None,
            "exactly one negative (a12 < 0)": "pos",
        }
        for name, cons in cases.items():
            if cons is None:
                a = [0] * len(EDGES)
                x, y = random.randrange(1, P), random.randrange(1, P)
                # P4-circle on {1,2,3,4}: a12=a34=x, a13=a24=y, a14=a23=-x-y
                for (e, v) in (((1, 2), x), ((3, 4), x), ((1, 3), y), ((2, 4), y), ((1, 4), -x - y), ((2, 3), -x - y)):
                    a[EIDX[e]] = (a[EIDX[e]] + v) % P
                u = random.randrange(1, P); w = random.randrange(1, P)
                for (e, v) in (((3, 4), u), ((3, 5), w), ((4, 5), -u - w)):
                    a[EIDX[e]] = (a[EIDX[e]] + v) % P
                print(f"{name:40s} H^*={aomoto_dims(a)}", flush=True)
            elif cons == "pos":
                a = [random.randrange(1, 1000) for _ in EDGES]
                a[EIDX[(1, 2)]] = (-sum(a[t] for t, e in enumerate(EDGES) if e != (1, 2))) % P
                print(f"{name:40s} H^*={aomoto_dims(a)}", flush=True)
            else:
                a, dim = nullspace_point(cons)
                print(f"{name:40s} dim={dim} H^*={aomoto_dims(a)}", flush=True)
    if SCAN:
        subsets = [frozenset(S) for r in range(2, n) for S in itertools.combinations(range(1, n + 1), r)]
        seen = {}
        maxc = int(sys.argv[3]) if len(sys.argv) > 3 else 3
        for c in range(0, maxc + 1):
            for combo in itertools.combinations(subsets, c):
                a, dim = nullspace_point([zs] + [S_vec(S) for S in combo])
                if dim == 0: continue
                d = aomoto_dims(a, upto=2)
                if d[1] or d[2]:
                    key = (dim, tuple(d))
                    seen.setdefault(key, []).append(sorted(map(sorted, combo)))
            print("codim", c, "resonant classes so far:", {k: len(v) for k, v in seen.items()}, flush=True)
        for k, v in seen.items():
            print("RESONANT", k, "count", len(v), "examples", v[:6])
    print("DONE")
