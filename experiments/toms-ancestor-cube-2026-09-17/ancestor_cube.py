#!/usr/bin/env python3
"""Ancestor-twisted sibling cube: the top-column value det[x_+^m - x_-^m].

Setting (see research/toms-ancestor-twisted-cubes-force-depth-k-over-2.md).
N = 2^L bottom swap nodes nu of a full binary tree; each has a factor CP^(j_b)
with class u_nu; each internal ancestor rho has CP^(j_rho) with class u_rho.
At stage M the block of nu is twisted by Gamma_nu = tensor of the ancestor lines
along the path, so

    x_(nu,+) = alpha u_nu + A_nu,   x_(nu,-) = beta u_nu + A_nu,
    A_nu = sum_(rho > nu) eps_(rho,nu) u_rho,  eps in {alpha, beta} by child.

Checks:
 1. chamber sum over (sigma, pi) equals (1/m_1!) det[x_+^(m_k) - x_-^(m_k)]
    symbolically for N = 2, 3 with free x and free ch(G) (generalized Step 3);
 2. the full determinant is non-zero in the truncated ring for N = 2, 4 and
    several j_b, twist pairs, and minimal ancestor room c_rho = a_rho * b_rho;
 3. the Vandermonde prod (A_nu' - A_nu) is non-zero in the truncated ancestor
    ring for N = 2, 4, 8 with room c_rho (it is then the single top monomial),
    and vanishes when every room is lowered by one;
 4. calibrations: alpha = beta gives 0; A = 0 (no ancestor twist) gives 0
    whenever the old Hall condition fails.
Exact integer arithmetic (and mod a large prime for the big Vandermondes).
"""
import itertools, json, math, sys
from fractions import Fraction

P = 2**61 - 1  # prime for the large checks


# ---------- truncated polynomial ring Q[u]/(u_i^(cap_i+1)) as sparse dicts ----------
def pmul(a, b, cap, mod=None):
    out = {}
    for ea, ca in a.items():
        for eb, cb in b.items():
            e = tuple(x + y for x, y in zip(ea, eb))
            if any(x > c for x, c in zip(e, cap)):
                continue
            v = out.get(e, 0) + ca * cb
            if mod:
                v %= mod
            out[e] = v
    return {e: c for e, c in out.items() if c}


def padd(a, b, s=1, mod=None):
    out = dict(a)
    for e, c in b.items():
        v = out.get(e, 0) + s * c
        if mod:
            v %= mod
        out[e] = v
    return {e: c for e, c in out.items() if c}


def lin(coeffs, nvar):
    out = {}
    for i, c in coeffs.items():
        if c:
            e = [0] * nvar
            e[i] = 1
            out[tuple(e)] = out.get(tuple(e), 0) + c
    return out


def ppow(a, m, cap, mod=None):
    nvar = len(cap)
    r = {tuple([0] * nvar): 1}
    for _ in range(m):
        r = pmul(r, a, cap, mod)
    return r


# ---------- the tree ----------
def tree(L):
    """Bottom nodes 0..N-1 (variables 0..N-1); ancestors at levels 1..L.
    Ancestor at level l, position q (q = nu >> l) gets a variable index.
    Returns (N, anc_index dict, nvar, paths) with paths[nu] = list of (var, bit)."""
    N = 2 ** L
    idx = {}
    k = N
    for l in range(1, L + 1):
        for q in range(N >> l):
            idx[(l, q)] = k
            k += 1
    paths = []
    for nu in range(N):
        p = []
        for l in range(1, L + 1):
            bit = (nu >> (l - 1)) & 1  # which child of the level-l ancestor
            p.append((idx[(l, nu >> l)], bit))
        paths.append(p)
    return N, idx, k, paths


def room(L, idx):
    """Minimal ancestor room c_rho = a_rho * b_rho (pairs with LCA rho)."""
    cap = {}
    for (l, q), v in idx.items():
        cap[v] = (2 ** (l - 1)) ** 2
    return cap


def x_lines(N, paths, nvar, alpha, beta, twist_anc=True):
    xs = []
    for nu in range(N):
        A = {}
        if twist_anc:
            for v, bit in paths[nu]:
                A[v] = A.get(v, 0) + (alpha if bit == 0 else beta)
        xp = dict(A); xp[nu] = xp.get(nu, 0) + alpha
        xm = dict(A); xm[nu] = xm.get(nu, 0) + beta
        xs.append((lin(xp, nvar), lin(xm, nvar)))
    return xs


def det_dp(entries, N, cap, mod=None):
    """det of N x N matrix of ring elements by Laplace DP over column subsets."""
    nvar = len(cap)
    one = {tuple([0] * nvar): 1}
    D = {0: one}
    for k in range(N):
        ND = {}
        for S, val in D.items():
            for c in range(N):
                if S >> c & 1:
                    continue
                # sign: number of chosen columns greater than c
                s = (-1) ** bin(S >> (c + 1)).count("1")
                term = pmul(val, entries[k][c], cap, mod)
                T = S | (1 << c)
                ND[T] = padd(ND.get(T, {}), term, s, mod)
        D = ND
    return D.get((1 << N) - 1, {})


def full_det(L, jb, alpha, beta, extra=0, twist_anc=True, mod=None):
    N, idx, nvar, paths = tree(L)
    capd = room(L, idx)
    cap = [jb] * N + [capd[v] + extra for v in range(N, nvar)]
    xs = x_lines(N, paths, nvar, alpha, beta, twist_anc)
    ms = list(range(1, N + 1))
    entries = []
    for m in ms:
        row = []
        for nu in range(N):
            xp, xm = xs[nu]
            row.append(padd(ppow(xp, m, cap, mod), ppow(xm, m, cap, mod), -1, mod))
        entries.append(row)
    d = det_dp(entries, N, cap, mod)
    return d, cap


def vandermonde(L, alpha, beta, cap_shift=0, mod=P):
    N, idx, nvar, paths = tree(L)
    capd = room(L, idx)
    anc = list(range(N, nvar))
    cap = [0] * N + [max(0, capd[v] + cap_shift) for v in anc]
    As = []
    for nu in range(N):
        A = {}
        for v, bit in paths[nu]:
            A[v] = A.get(v, 0) + (alpha if bit == 0 else beta)
        As.append(A)
    prod = {tuple([0] * nvar): 1}
    for a in range(N):
        for b in range(a + 1, N):
            diff = dict(As[b])
            for v, c in As[a].items():
                diff[v] = diff.get(v, 0) - c
            prod = pmul(prod, lin(diff, nvar), cap, mod)
            if not prod:
                return prod, cap
    return prod, cap


def chamber_check(N, ms):
    import sympy as sp
    from sympy.combinatorics import Permutation
    xp = sp.symbols("xp0:%d" % N)
    xm = sp.symbols("xm0:%d" % N)
    chG = sp.Symbol("chG")
    total = 0
    for sig in itertools.product([1, -1], repeat=N):
        x = [xp[i] if sig[i] == 1 else xm[i] for i in range(N)]
        for pi in itertools.permutations(range(N)):
            sgn = Permutation(list(pi)).signature()
            term = (chG + x[pi[0]] ** ms[0] / sp.factorial(ms[0]))
            for k in range(1, N):
                term *= x[pi[k]] ** ms[k]
            total += sgn * math.prod(sig) * term
    M = sp.Matrix(N, N, lambda k, nu: xp[nu] ** ms[k] - xm[nu] ** ms[k])
    return sp.expand(total - M.det() / sp.factorial(ms[0])) == 0


def main():
    res = {"chamber_sum_equals_det": {}, "full_det": [], "vandermonde": [], "calibration": []}
    for N, ms in [(2, (1, 2)), (2, (3, 1)), (3, (1, 2, 3)), (3, (2, 1, 4))]:
        res["chamber_sum_equals_det"][f"N={N},m={ms}"] = chamber_check(N, ms)
    twists = [(1, 2), (-1, -2), (1, -1), (-2, -1)]
    for L, jbs in [(1, [1, 2, 3]), (2, [1, 2, 3])]:
        for jb in jbs:
            for al, be in twists:
                d, cap = full_det(L, jb, al, be)
                res["full_det"].append({"N": 2 ** L, "j_bottom": jb, "alpha": al, "beta": be,
                                        "cap": cap, "nonzero": bool(d), "terms": len(d)})
    # calibrations
    for L, jb in [(1, 1), (2, 1), (2, 3)]:
        d, _ = full_det(L, jb, 1, 1)
        res["calibration"].append({"case": "alpha=beta", "N": 2 ** L, "j_bottom": jb, "nonzero": bool(d)})
        d, _ = full_det(L, jb, 1, 2, twist_anc=False)
        res["calibration"].append({"case": "no ancestor twist", "N": 2 ** L, "j_bottom": jb,
                                   "old_hall_holds": jb >= 2 ** L, "nonzero": bool(d)})
    for L in range(1, 4):
        for al, be in [(1, 2), (1, -1)]:
            v, cap = vandermonde(L, al, be)
            lead = max(v) if v else None
            res["vandermonde"].append({"N": 2 ** L, "alpha": al, "beta": be, "nonzero": bool(v),
                                       "terms": len(v), "degree": 2 ** L * (2 ** L - 1) // 2})
            if L <= 3:
                v2, _ = vandermonde(L, al, be, cap_shift=-1)
                res["vandermonde"][-1]["room_minus_one_nonzero"] = bool(v2)
            print(res["vandermonde"][-1], flush=True)
    print(json.dumps(res["chamber_sum_equals_det"]))
    for r in res["full_det"]:
        print({k: r[k] for k in ("N", "j_bottom", "alpha", "beta", "nonzero", "terms")})
    for r in res["calibration"]:
        print(r)
    json.dump(res, open(sys.argv[1] if len(sys.argv) > 1 else "results.json", "w"), indent=1)


if __name__ == "__main__":
    main()
