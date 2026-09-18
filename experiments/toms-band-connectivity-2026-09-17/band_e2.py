"""Integral E_2 of the eigenvalue-gap cover of the band space X_(g,N).

X_(g,N) = { psd Q in M_n : g+1 <= rank Q <= g+N },  n -> infinity.
Cover: U_k = { lambda_(g+k) > lambda_(g+k+1) },  k = 1..N  (lambda_(g+N+1) = 0).
For T = {t_1 < ... < t_s} the intersection U_T deformation retracts onto the partial flag
manifold of flags W_(g+t_1) < ... < W_(g+t_s): shrink the eigenvalues below lambda_(g+t_s)
to 0 and make the eigenvalues inside each block equal (convex).  So
    H^*(U_T; Z) = Z[c(B_1)] (x) ... (x) Z[c(B_s)],
    B_1 = W_(g+t_1) of rank g+t_1,  B_i = W_(g+t_i)/W_(g+t_(i-1)) of rank t_i - t_(i-1).
For T < T' the restriction H^*(U_T) -> H^*(U_T') is the Whitney sum formula (each block of
T is a sum of consecutive blocks of T').  All U_T are non-empty, so the nerve is a simplex.

The Mayer-Vietoris (Cech) spectral sequence has
    E_1^(p,q) = (+)_(|T| = p+1) H^q(U_T; Z),   d_1 = alternating sum of restrictions,
and converges to H^(p+q)(X; Z).  This script computes E_2^(p,q) over Z (free rank and
torsion, via Smith normal form in python-flint) for all p + q <= Dmax.

If E_2^(p,q) = 0 for 0 < p+q <= D and E_2 is torsion-free in total degree D+1, then
H^k(X; Z) = 0 for 0 < k <= D and H^(D+1)(X; Z) is torsion-free; X is simply connected
(van Kampen: the U_T are simply connected and connected), so X is D-connected (Hurewicz +
universal coefficients, X of finite type).

Usage:  python3 band_e2.py N Dmax [g|stable] [--mod=p1,p2,...]
  g omitted or 'stable': rank W unbounded.  --mod: ranks over F_p instead of Smith form;
  then 'free' is computed from the smallest rank over the primes (the largest
  dim E_2 (x) F_p over the listed p), and 'torsion' lists the primes whose rank dropped
  below the others (the mod-p E_2 is larger there).  E_2 (x) F_p = 0 in a range for all
  listed p, together with the large prime (a proxy for Q), is what the N = 4 check uses.
"""
import itertools
import json
import sys
from functools import lru_cache

import flint


def partitions(d, maxpart):
    """Partitions of d with parts <= maxpart, as descending tuples."""
    out = []

    def rec(rem, mx, cur):
        if rem == 0:
            out.append(tuple(cur))
            return
        for k in range(min(rem, mx), 0, -1):
            cur.append(k)
            rec(rem - k, k, cur)
            cur.pop()

    rec(d, maxpart, [])
    return out


def block_ranks(T, g):
    r = [None if g is None else g + T[0]]
    for a, b in zip(T, T[1:]):
        r.append(b - a)
    return r


def basis(T, g, d):
    ranks = block_ranks(T, g)
    s = len(ranks)
    res = []
    for comp in itertools.product(range(d + 1), repeat=s):
        if sum(comp) != d:
            continue
        lists = [partitions(comp[i], d if ranks[i] is None else ranks[i]) for i in range(s)]
        for tup in itertools.product(*lists):
            res.append(tup)
    return res


def mono_mul(a, b):
    return tuple(tuple(sorted(x + y, reverse=True)) for x, y in zip(a, b))


def poly_mul(P, R):
    out = {}
    for ka, va in P.items():
        for kb, vb in R.items():
            k = mono_mul(ka, kb)
            out[k] = out.get(k, 0) + va * vb
    return {k: v for k, v in out.items() if v}


def make_restriction(T, Tp, g):
    """Return function mapping a monomial of H(U_T) to a polynomial in H(U_Tp)."""
    rp = block_ranks(Tp, g)
    sp_ = len(Tp)
    # block i of T = W_(g+T[i]) / W_(g+T[i-1]); in Tp it is the sum of blocks with
    # index in (pos(T[i-1]), pos(T[i])]
    pos = {t: i for i, t in enumerate(Tp)}
    groups = []
    prev = -1
    for t in T:
        groups.append(list(range(prev + 1, pos[t] + 1)))
        prev = pos[t]

    @lru_cache(maxsize=None)
    def chern_of_sum(gi, k):
        """c_k of the sum of the Tp-blocks in groups[gi], as a polynomial."""
        blocks = groups[gi]
        P = {tuple(() for _ in range(sp_)): 1}
        # total chern class product, keep degree k part
        res = {}
        for ks in itertools.product(range(k + 1), repeat=len(blocks)):
            if sum(ks) != k:
                continue
            ok = True
            m = [() for _ in range(sp_)]
            for b, kk in zip(blocks, ks):
                if kk == 0:
                    continue
                if rp[b] is not None and kk > rp[b]:
                    ok = False
                    break
                m[b] = (kk,)
            if ok:
                key = tuple(m)
                res[key] = res.get(key, 0) + 1
        return res

    @lru_cache(maxsize=None)
    def image(mono):
        P = {tuple(() for _ in range(sp_)): 1}
        for gi, part in enumerate(mono):
            for k in part:
                P = poly_mul(P, chern_of_sum(gi, k))
        return P

    return image


def e2(N, Dmax, g=None, primes=None):
    """primes=None: over Z (Smith normal form).  primes=[p, ...]: ranks over F_p for each p;
    then 'free' is the dimension of E_2 (x) F_p computed from ranks mod p, reported per p."""
    subsets = {p: [T for T in itertools.combinations(range(1, N + 1), p + 1)] for p in range(N)}
    results = {}
    restr = {}
    for p in range(N - 1):
        for Tp in subsets[p + 1]:
            for i in range(len(Tp)):
                T = Tp[:i] + Tp[i + 1:]
                restr[(T, Tp)] = (make_restriction(T, Tp, g), (-1) ** i)
    for d in range(0, Dmax // 2 + 1):
        q = 2 * d
        bases = {p: [(T, m) for T in subsets[p] for m in basis(T, g, d)] for p in range(N)}
        index = {p: {bm: k for k, bm in enumerate(bases[p])} for p in range(N)}
        ranks, divs = {}, {}
        for p in range(N - 1):
            rows, cols = len(bases[p + 1]), len(bases[p])
            if rows == 0 or cols == 0:
                ranks[p], divs[p] = 0, []
                continue
            M = [[0] * cols for _ in range(rows)]
            for c, (T, m) in enumerate(bases[p]):
                for Tp in subsets[p + 1]:
                    if (T, Tp) not in restr:
                        continue
                    f, sgn = restr[(T, Tp)]
                    for km, v in f(m).items():
                        M[index[p + 1][(Tp, km)]][c] += sgn * v
            if primes is None:
                A = flint.fmpz_mat(M)
                S = A.snf()
                diag = [int(S[i, i]) for i in range(min(rows, cols))]
                nz = [abs(x) for x in diag if x != 0]
                ranks[p] = len(nz)
                divs[p] = sorted(x for x in nz if x != 1)
            else:
                rks = [flint.nmod_mat(M, pr).rank() for pr in primes]
                ranks[p] = min(rks)
                divs[p] = [pr for pr, rk in zip(primes, rks) if rk < max(rks)]
        print(f"d={d} dims={[len(bases[p]) for p in range(N)]} ranks={ranks} divs={divs}", file=sys.stderr, flush=True)
        for p in range(N):
            if p + q > Dmax:
                continue
            dim = len(bases[p])
            rk_out = ranks.get(p, 0)
            rk_in = ranks.get(p - 1, 0)
            tors = divs.get(p - 1, [])
            results[(p, q)] = {"dim_E1": dim, "free": dim - rk_out - rk_in, "torsion": tors}
    return results


def main():
    N = int(sys.argv[1])
    Dmax = int(sys.argv[2])
    args = [a for a in sys.argv[3:] if not a.startswith("--mod=")]
    mods = [a for a in sys.argv[3:] if a.startswith("--mod=")]
    g = int(args[0]) if args and args[0] != "stable" else None
    primes = [int(x) for x in mods[0][6:].split(",")] if mods else None
    res = e2(N, Dmax, g, primes)
    nonzero = {f"{p},{q}": v for (p, q), v in sorted(res.items()) if v["free"] or v["torsion"]}
    tot = {}
    for (p, q), v in res.items():
        t = tot.setdefault(p + q, {"free": 0, "torsion": []})
        t["free"] += v["free"]
        t["torsion"] += v["torsion"]
    conn = None
    for k in range(1, Dmax + 1):
        t = tot.get(k, {"free": 0, "torsion": []})
        if t["free"] or t["torsion"]:
            conn = k - 1
            break
    out = {"N": N, "g": g, "Dmax": Dmax, "primes": primes, "nonzero_E2": nonzero,
           "by_total_degree": {k: tot[k] for k in sorted(tot)},
           "first_nonzero_total_degree": None if conn is None else conn + 1}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
