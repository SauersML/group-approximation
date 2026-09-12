#!/usr/bin/env python3
"""2-adic analysis of the normalised system uv = 1, eps(u) = eps(v) = 1 on (S, T).

Input: system.json (from gsp.py) and f2points.txt (from f2enum; hex u v, bit i = coordinate i).
For every F_2-point xbar:
  * rank over F_2 of the Jacobian J(xbar) (123 x 42), kernel dimension kappa;
  * rank over Q (via rank mod two large primes, a lower bound that is exact once 42);
  * if xbar is trivial (weight-one u and v): check it is an exact integer solution;
  * 2-adic lifting: Sol_1 = {xbar}; Sol_{k+1} = {x + 2^k d : x in Sol_k, d in F_2^42,
    F(x)/2^k + J(xbar) d = 0 mod 2}.  (Exact because F is quadratic and 2k >= k+1.)
Lifting stops when Sol_k is empty, or at depth MAXK, or when |Sol_k| exceeds CAP.
"""
import json, sys

sysd = json.load(open("system.json"))
prod, K, eid = sysd["prod"], sysd["K"], sysd["eid"]
n, NV = 21, 42
NEQ = K + 2
MAXK = int(sys.argv[1]) if len(sys.argv) > 1 else 8
CAP = 1 << 20
eqs = [[] for _ in range(K)]
for i in range(n):
    for j in range(n):
        eqs[prod[i][j]].append((i, j))

def F(x):
    u, v = x[:n], x[n:]
    out = [sum(u[i] * v[j] for i, j in eqs[k]) - (1 if k == eid else 0) for k in range(K)]
    return out + [sum(u) - 1, sum(v) - 1]

def jac(x):
    u, v = x[:n], x[n:]
    rows = []
    for k in range(K):
        r = [0] * NV
        for i, j in eqs[k]:
            r[i] += v[j]
            r[n + j] += u[i]
        rows.append(r)
    rows.append([1] * n + [0] * n)
    rows.append([0] * n + [1] * n)
    return rows

def rank_mod(rows, p):
    M = [[c % p for c in r] for r in rows]
    rk, col = 0, 0
    ncols = len(M[0])
    for col in range(ncols):
        piv = next((t for t in range(rk, len(M)) if M[t][col]), None)
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        inv = pow(M[rk][col], p - 2, p) if p > 2 else 1
        M[rk] = [(c * inv) % p for c in M[rk]]
        for t in range(len(M)):
            if t != rk and M[t][col]:
                f = M[t][col]
                M[t] = [(a - f * b) % p for a, b in zip(M[t], M[rk])]
        rk += 1
    return rk

class F2Solver:
    """Fixed matrix over F_2; solve J d = b for many right-hand sides b."""
    def __init__(self, rows):
        self.m = len(rows)
        R = []
        for idx, r in enumerate(rows):
            mask = 0
            for c, val in enumerate(r):
                if val & 1:
                    mask |= 1 << c
            R.append([mask, 1 << idx])  # [row bits, tag of original rows combined]
        pivots = []
        rk = 0
        for col in range(NV):
            piv = next((t for t in range(rk, self.m) if R[t][0] >> col & 1), None)
            if piv is None:
                continue
            R[rk], R[piv] = R[piv], R[rk]
            for t in range(self.m):
                if t != rk and R[t][0] >> col & 1:
                    R[t][0] ^= R[rk][0]
                    R[t][1] ^= R[rk][1]
            pivots.append(col)
            rk += 1
        self.rank = rk
        self.pivrows = [(pivots[t], R[t][0], R[t][1]) for t in range(rk)]
        self.zerotags = [R[t][1] for t in range(rk, self.m)]
        pivset = set(pivots)
        self.free = [c for c in range(NV) if c not in pivset]
        self.kernel = []
        for f in self.free:
            vec = 1 << f
            for pc, rowbits, _ in self.pivrows:
                if rowbits >> f & 1:
                    vec |= 1 << pc
            self.kernel.append(vec)

    def solve(self, bmask):
        for tag in self.zerotags:
            if bin(tag & bmask).count("1") & 1:
                return None
        d = 0
        for pc, _, tag in self.pivrows:
            if bin(tag & bmask).count("1") & 1:
                d |= 1 << pc
        return d

    def all_solutions(self, bmask):
        d0 = self.solve(bmask)
        if d0 is None:
            return []
        sols = [d0]
        for kv in self.kernel:
            sols += [s ^ kv for s in sols]
        return sols

pts = []
for line in open("f2points.txt"):
    uh, vh = line.split()
    uu, vv = int(uh, 16), int(vh, 16)
    pts.append([(uu >> i) & 1 for i in range(n)] + [(vv >> j) & 1 for j in range(n)])
print("F_2 points:", len(pts))
report = []
for x0 in pts:
    wu, wv = sum(x0[:n]), sum(x0[n:])
    trivial = (wu == 1 and wv == 1)
    Fx0 = F(x0)
    exact = all(c == 0 for c in Fx0)
    assert all(c % 2 == 0 for c in Fx0), "not an F_2 point"
    J = jac(x0)
    solver = F2Solver(J)
    kappa = NV - solver.rank
    rq = max(rank_mod(J, 1000003), rank_mod(J, 998244353))
    levels = [1]
    sol = [tuple(x0)]
    k = 1
    status = "open"
    while k < MAXK:
        nxt = []
        for x in sol:
            Fx = F(list(x))
            assert all(c % (1 << k) == 0 for c in Fx)
            b = 0
            for idx, c in enumerate(Fx):
                if (c >> k) & 1:
                    b |= 1 << idx
            for d in solver.all_solutions(b):
                nxt.append(tuple(x[c] + ((d >> c) & 1) * (1 << k) for c in range(NV)))
                if len(nxt) > CAP:
                    break
            if len(nxt) > CAP:
                break
        k += 1
        levels.append(len(nxt))
        sol = nxt
        if not sol:
            status = f"no solutions mod 2^{k}"
            break
        if len(sol) > CAP:
            status = f"cap exceeded at 2^{k}"
            break
    if trivial and sol:
        # the exact trivial solution must survive at every level
        assert tuple(x0) in set(sol) or status.startswith("cap")
    rec = {"u_support": [i for i in range(n) if x0[i]], "v_support": [j for j in range(n) if x0[n + j]],
           "trivial": trivial, "exact_integer_solution": exact, "rank_F2": solver.rank, "kappa": kappa,
           "rank_Q_lower": rq, "level_counts": levels, "status": status}
    report.append(rec)
    print(json.dumps(rec))
json.dump(report, open("lift_report.json", "w"), indent=1)
