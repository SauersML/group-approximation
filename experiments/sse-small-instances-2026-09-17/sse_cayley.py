#!/usr/bin/env python3
"""Exact small-set expansion profiles of weighted Cayley graphs Cay(F_2^k, w)
versus three certificates.

Quantity.  For S subset F_2^k, |S| = s, delta = s/N (N = 2^k), weights w_a >= 0
on nonzero a with W = sum w_a:

    stay(S) = 1 - Phi(S) = sum_a w_a |S cap (S+a)| / (W s).

We compute, for each graph and each s:

  EXACT  max_S stay(S)             (MILP via HiGHS; cross-checked by C brute force)
  SUB    max over subgroups H with |H| = s of stay(H)  (s a power of two)
  SDP    translation-symmetrised basic SDP = Delsarte LP over g(x) = |S cap (S+x)|/N:
             g(0) = delta, 0 <= g <= delta, sum_x g = N delta^2, ghat(y) >= 0,
             maximise sum_a w_a g(a) / (W delta).
         (Averaging an optimal Gram matrix over translations is lossless, and a
          translation-invariant Gram matrix M(x,y) = g(x-y) is PSD with M - xx^T PSD
          iff ghat >= 0 with ghat(0) = delta^2; so this LP *is* the basic SDP.)
  INT    Delsarte LP with the integrality N g(x) in 2Z for x != 0 (a MILP; still a
         relaxation of EXACT, stronger than SDP).
  EIG    best pure spectral certificate: max sum_y lambda_y a_y subject to
         a_0 = delta^2, sum a = delta, 0 <= a_y <= delta^2 (Parseval + |fhat| <= delta),
         = delta * sum_{i<m} lambda_i + (1 - m delta) lambda_m, m = floor(1/delta).
         It dominates the threshold-rank bound lambda_{r+1} + r delta.

Only standard library + numpy + scipy.
"""
import itertools, json, math, sys
import numpy as np
from scipy.optimize import milp, linprog, LinearConstraint, Bounds
from scipy.sparse import lil_matrix, csr_matrix

def popcount(x):
    return bin(x).count("1")

def hadamard(k):
    N = 1 << k
    H = np.empty((N, N))
    for x in range(N):
        for y in range(N):
            H[x, y] = -1.0 if popcount(x & y) & 1 else 1.0
    return H

_HCACHE = {}
def H_of(k):
    if k not in _HCACHE:
        _HCACHE[k] = hadamard(k)
    return _HCACHE[k]

def eigenvalues(k, w):
    H = H_of(k)
    W = sum(w.values())
    vec = np.zeros(1 << k)
    for a, wa in w.items():
        vec[a] += wa
    return H @ vec / W   # lambda_y = sum_a w_a (-1)^{a.y} / W

def eig_cert(k, w, s):
    N = 1 << k
    d = s / N
    lam = np.sort(eigenvalues(k, w))[::-1]
    m = int(math.floor(1 / d + 1e-12))
    tail = lam[m] if m < N else 0.0
    return float(d * lam[:m].sum() + (1 - m * d) * tail)

def sdp_cert(k, w, s, integral=False):
    """Delsarte LP (= symmetrised basic SDP).  integral=True adds N g(x) = 2 h(x), h in Z."""
    N = 1 << k
    d = s / N
    W = sum(w.values())
    H = H_of(k)
    # variables h(x) = N g(x) / 2 for x != 0 (count of unordered pairs); g(0) fixed.
    # N g(x) = |S cap (S+x)| in [0, s];  sum_{x != 0} |S cap (S+x)| = s^2 - s.
    n = N - 1
    c = np.zeros(n)
    for a, wa in w.items():
        c[a - 1] -= 2 * wa / (W * s)          # maximise sum w_a |S cap S+a| / (W s)
    A_eq = np.ones((1, n)) * 2
    b_eq = [s * s - s]
    # ghat(y) >= 0:  s + sum_{x != 0} 2 h(x) (-1)^{x.y} >= 0
    A_ub = -2 * H[:, 1:]
    b_ub = np.full(N, float(s))
    ub = s / 2
    if not integral:
        res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                      bounds=[(0, ub)] * n, method="highs")
        assert res.status == 0, res.message
        return float(-res.fun)
    cons = [LinearConstraint(A_ub, -np.inf, b_ub), LinearConstraint(A_eq, b_eq, b_eq)]
    res = milp(c, constraints=cons, integrality=np.ones(n), bounds=Bounds(0, math.floor(ub)),
               options={"time_limit": 120, "mip_rel_gap": 1e-9})
    if res.status != 0:
        return None
    return float(-res.fun)

def stay(k, w, S):
    Sset = set(S)
    W = sum(w.values())
    tot = 0.0
    for a, wa in w.items():
        tot += wa * sum(1 for v in Sset if v ^ a in Sset)
    return tot / (W * len(Sset))

def exact_milp(k, w, s, time_limit=600):
    """max_S stay(S), |S| = s, 0 in S. Returns (value, witness, optimal_flag)."""
    N = 1 << k
    W = sum(w.values())
    edges = []
    for a, wa in w.items():
        if wa <= 0:
            continue
        for v in range(N):
            u = v ^ a
            if v < u:
                edges.append((v, u, wa))
    nE = len(edges)
    nv = N + nE
    c = np.zeros(nv)
    for i, (v, u, wa) in enumerate(edges):
        c[N + i] = -2 * wa / (W * s)
    A = lil_matrix((2 * nE + 1, nv))
    lo = np.full(2 * nE + 1, -np.inf)
    hi = np.zeros(2 * nE + 1)
    for i, (v, u, wa) in enumerate(edges):
        A[2 * i, N + i] = 1; A[2 * i, v] = -1
        A[2 * i + 1, N + i] = 1; A[2 * i + 1, u] = -1
    A[2 * nE, :N] = 1
    lo[2 * nE] = hi[2 * nE] = s
    lb = np.zeros(nv); ub = np.ones(nv); lb[0] = 1
    integ = np.zeros(nv); integ[:N] = 1
    res = milp(c, constraints=[LinearConstraint(csr_matrix(A), lo, hi)], integrality=integ,
               bounds=Bounds(lb, ub), options={"time_limit": time_limit, "mip_rel_gap": 1e-9})
    if res.x is None:
        return None, None, False
    S = [v for v in range(N) if res.x[v] > 0.5]
    val = stay(k, w, S)
    optimal = res.status == 0
    # objective is (integer)/(W s) when weights are integers: gap < 1/(W s) means optimal
    return val, S, optimal

import os, subprocess, tempfile
_EXE = None
def _exe():
    global _EXE
    if _EXE is None:
        here = os.path.dirname(os.path.abspath(__file__))
        out = os.path.join(tempfile.gettempdir(), "sse_exact_bin")
        subprocess.run(["gcc", "-O2", "-o", out, os.path.join(here, "sse_exact.c")], check=True)
        _EXE = out
    return _EXE

def exact_c(k, w, s, lower=0.0, timeout=3600):
    """Exact branch and bound (integer weights). Returns (stay, witness, nodes)."""
    N = 1 << k
    W = sum(w.values())
    arr = [0] * N
    for a, wa in w.items():
        assert wa == int(wa)
        arr[a] += int(wa)
    lb = int(math.floor(lower * W * s / 2 + 1e-9))
    inp = f"{k} {s} {lb}\n" + " ".join(map(str, arr)) + "\n"
    r = subprocess.run([_exe()], input=inp, capture_output=True, text=True, timeout=timeout)
    lines = r.stdout.strip().split("\n")
    P = int(lines[0]); S = list(map(int, lines[1].split())); nodes = int(lines[2])
    val = 2 * P / (W * s)
    assert abs(stay(k, w, S) - val) < 1e-12
    return val, S, nodes

def subspaces(k, j):
    """All j-dim subspaces of F_2^k, as sorted element lists (via RREF enumeration)."""
    out = set()
    # enumerate pivot sets and free entries
    for piv in itertools.combinations(range(k), j):
        free = [(r, col) for r in range(j) for col in range(piv[r] + 1, k) if col not in piv]
        for bits in range(1 << len(free)):
            rows = [1 << (k - 1 - piv[r]) for r in range(j)]
            for t, (r, col) in enumerate(free):
                if bits >> t & 1:
                    rows[r] |= 1 << (k - 1 - col)
            span = {0}
            for rw in rows:
                span |= {x ^ rw for x in span}
            out.add(tuple(sorted(span)))
    return [list(t) for t in out]

_SUBCACHE = {}
def best_subspace(k, w, s):
    j = s.bit_length() - 1
    if 1 << j != s:
        return None
    key = (k, j)
    if key not in _SUBCACHE:
        _SUBCACHE[key] = subspaces(k, j)
    W = sum(w.values())
    best = 0.0
    for Hs in _SUBCACHE[key]:
        hs = set(Hs)
        val = sum(wa for a, wa in w.items() if a in hs) / W
        best = max(best, val)
    return best

# ---------------------------------------------------------------- graph families
def vec(bits):
    x = 0
    for b in bits:
        x = (x << 1) | b
    return x

def hypercube(k):
    return {1 << i: 1 for i in range(k)}

def noisy_cube(k, num, den):
    """Weighted Cayley graph of the rho-noisy cube, rho = num/den, integer weights
    num^|a| (den-num)^(k-|a|) (a != 0)."""
    return {a: num ** popcount(a) * (den - num) ** (k - popcount(a)) for a in range(1, 1 << k)}

def hadamard_short_code(m, num, den):
    """Quotient of the rho-noisy cube on F_2^(2^m) by RM(m-2,m) = RM(1,m)^perp:
    vertex space F_2^(m+1), coordinate z in F_2^m maps to (1,z).  Integer weights."""
    n = 1 << m
    k = m + 1
    pts = [(1 << m) | z for z in range(n)]
    w = {}
    # sum over noise vectors grouped by support: 2^n supports, n <= 16 fine for m <= 4
    for supp in range(1 << n):
        t = popcount(supp)
        if t == 0:
            continue
        img = 0
        for i in range(n):
            if supp >> i & 1:
                img ^= pts[i]
        if img == 0:
            continue
        w[img] = w.get(img, 0) + num ** t * (den - num) ** (n - t)
    return k, w

def profile(k, w, sizes, exact=True, integral=True, time_limit=600):
    rows = []
    for s in sizes:
        row = {"s": s, "delta": s / (1 << k)}
        row["EIG"] = eig_cert(k, w, s)
        row["SDP"] = sdp_cert(k, w, s)
        if integral:
            row["INT"] = sdp_cert(k, w, s, integral=True)
        row["SUB"] = best_subspace(k, w, s)
        if exact:
            v, S, opt = exact_milp(k, w, s, time_limit)
            row["EXACT"] = v; row["optimal"] = opt; row["witness"] = S
        rows.append(row)
    return rows

if __name__ == "__main__":
    k = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    for name, w in [("hypercube", hypercube(k)), ("noisy 1/4", noisy_cube(k, 1, 4))]:
        print(name)
        for r in profile(k, w, [2, 4, 8]):
            print({x: (round(y, 4) if isinstance(y, float) else y) for x, y in r.items() if x != "witness"})
