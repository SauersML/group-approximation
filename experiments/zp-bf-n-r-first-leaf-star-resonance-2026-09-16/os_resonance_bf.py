#!/usr/bin/env python3
"""Aomoto complexes (A(P_k), a /\\) for the braid characters Phi_k of bF_{n,r}.

Context: Cairn hole bf-n-r-twist-invisible-braid-characters-in-sigma-infinity. For phi in W_0 (full-twist
invisible) Lemma 5 of research/artifacts/zp-pure-braided-bht-sigma-2026-09-13.md reduces membership in
Sigma^j(bF_{n,r}) to [Phi_k] in Sigma^j(P_k) for all large k. The resonance upper bound
(arrangement-bnsr-invariants-avoid-real-resonance) says [Phi_k] is NOT in Sigma^q(P_k) if
H^i(A(P_k), Phi_k /\\) != 0 for some i <= q. This script computes those dimensions.

Scope (evidence only):
  * a vanishing dim H^i over F_p implies vanishing over Q (rank over F_p <= rank over Q), so "H^i = 0" is exact;
  * a nonvanishing dim over F_p is reported for two primes and is strong evidence, not a proof, over Q;
  * vanishing of H^{<=q} does not prove [Phi_k] in Sigma^q(P_k) (that needs the open conjecture
    pure-braid-bnsr-complements-are-real-resonance-varieties); it only shows the resonance bound gives no hole.

OS algebra of the braid arrangement: generators e_{ij}, i < j <= k. Normal (nbc) basis: monomials with distinct
columns j_1 < ... < j_p. Arnold relation for a < b < l: e_{al} e_{bl} = e_{ab} e_{bl} - e_{ab} e_{al}.

Usage: timeout 600 python3 os_resonance_bf.py [main|deep]
  (stage "main", the default, writes results.json; stage "deep" writes results_deep.json; both next to this file)
"""
import itertools, json, os, random, sys, time
sys.dont_write_bytecode = True  # the cross-check imports a module from research/artifacts; write no caches there
from functools import lru_cache
from fractions import Fraction

import numpy as np

PRIMES = (2147483647, 1000000007)
HERE = os.path.dirname(os.path.abspath(__file__))


# ---------------------------------------------------------------- OS algebra of the braid arrangement
@lru_cache(maxsize=None)
def lmul(a, b, mono):
    """e_{ab} * mono for a normal monomial mono (tuple of (row, col), columns increasing).

    Returns a tuple of (normal monomial, integer coefficient)."""
    cols = [j for (_, j) in mono]
    if b not in cols:
        pos = sum(1 for j in cols if j < b)
        return ((mono[:pos] + ((a, b),) + mono[pos:], -1 if pos % 2 else 1),)
    pos = cols.index(b)
    c = mono[pos][0]
    if c == a:
        return ()
    lo, hi = min(a, c), max(a, c)
    # e_ab * (pre, e_cb, suf) = e_{lo,hi} * [(pre, e_cb, suf) - (pre, e_ab, suf)]   (signs cancel; see artifact)
    acc = {}
    for m, v in lmul(lo, hi, mono):
        acc[m] = acc.get(m, 0) + v
    for m, v in lmul(lo, hi, mono[:pos] + ((a, b),) + mono[pos + 1:]):
        acc[m] = acc.get(m, 0) - v
    return tuple((m, v) for m, v in acc.items() if v)


@lru_cache(maxsize=None)
def basis(k, p):
    out = []
    for cols in itertools.combinations(range(2, k + 1), p):
        for rows in itertools.product(*[range(1, j) for j in cols]):
            out.append(tuple(zip(rows, cols)))
    return tuple(out)


@lru_cache(maxsize=None)
def bindex(k, p):
    return {m: t for t, m in enumerate(basis(k, p))}


def stirling_row(k):
    """coefficients of prod_{j=1}^{k-1} (1 + j t)."""
    poly = [1]
    for j in range(1, k):
        new = poly + [0]
        for t in range(len(poly)):
            new[t + 1] += j * poly[t]
        poly = new
    return poly


def dmatrix(k, p, a, P):
    """matrix of x -> a /\\ x from A^p to A^{p+1} over F_P; a: dict (i,j) -> int."""
    src, tgt = basis(k, p), bindex(k, p + 1)
    M = np.zeros((len(tgt), len(src)), dtype=np.int64)
    for col, m in enumerate(src):
        for (i, j), v in a.items():
            if v % P == 0:
                continue
            for mm, c in lmul(i, j, m):
                M[tgt[mm], col] = (M[tgt[mm], col] + v * c) % P
    return M


def rank_mod(M, P):
    """rank over F_P; M must already be reduced mod P and is destroyed."""
    R, C = M.shape
    r = 0
    for c in range(C):
        if r == R:
            break
        nz = np.flatnonzero(M[r:, c])
        if nz.size == 0:
            continue
        piv = r + int(nz[0])
        if piv != r:
            M[[r, piv]] = M[[piv, r]]
        inv = pow(int(M[r, c]), P - 2, P)
        M[r, c:] = (M[r, c:] * inv) % P
        below = r + 1 + np.flatnonzero(M[r + 1:, c])
        if below.size:
            f = M[below, c].copy()
            M[below, c:] = (M[below, c:] - (f[:, None] * M[r, c:][None, :]) % P) % P
        r += 1
    return r


def aomoto(k, a, maxdeg, P):
    """[dim_{F_P} H^i(A(P_k), a /\\)] for i = 0..maxdeg."""
    top = k - 1
    ranks = {}
    for p in range(0, min(maxdeg, top - 1) + 1):
        ranks[p] = rank_mod(dmatrix(k, p, a, P), P)
    dims = []
    for i in range(0, min(maxdeg, top) + 1):
        rin = ranks.get(i - 1, 0)
        rout = ranks[i] if i <= top - 1 else 0
        dims.append(len(basis(k, i)) - rin - rout)
    return dims


def dd_zero(k, a, p, P):
    """check (a/\\)(a/\\) = 0 on A^p (small primes-free check with exact integer arithmetic)."""
    D1, D2 = dmatrix(k, p, a, P), dmatrix(k, p + 1, a, P)
    D1 = np.where(D1 > P // 2, D1 - P, D1)
    D2 = np.where(D2 > P // 2, D2 - P, D2)
    return not np.any(D2 @ D1) if D1.size and D2.size else True


# ---------------------------------------------------------------- characters of bF_{n,r} via leaf-pair types
def pair_type(i, j, k, d):
    A = ("E",) if i == 1 else ("P", (i - 1) % d)
    G = ("E",) if j == i + 1 else ("P", (j - i - 1) % d)
    B = ("E",) if j == k else ("P", (k - j) % d)
    return A, G, B


def phi_value(data, i, j, k, n, r):
    """Theorem 1 (zp-pure-braided-bht-characters-2026-09-13.md): value of phi on A_{ij} in a k-leaf forest."""
    d = n - 1
    PPP, EPP, PPE, PEP, EPE = data["PPP"], data["EPP"], data["PPE"], data["PEP"], data["EPE"]
    EEP = EPP[0] + PEP[0] - PPP[0][0]
    PEE = PEP[(r - 2) % d] + PPE[(r - 2) % d] - PPP[(r - 2) % d][0]
    EEE = EEP + EPE - EPP[0]
    A, G, B = pair_type(i, j, k, d)
    key = A[0] + G[0] + B[0]
    if key == "PPP":
        return PPP[A[1]][G[1]]
    if key == "EPP":
        return EPP[G[1]]
    if key == "PPE":
        return PPE[A[1]]
    if key == "PEP":
        return PEP[A[1]]
    if key == "EPE":
        return EPE
    if key == "EEP":
        return EEP
    if key == "PEE":
        return PEE
    return EEE


def Phi(data, n, r, k):
    return {(i, j): phi_value(data, i, j, k, n, r) for j in range(2, k + 1) for i in range(1, j)}


def data_constraints_ok(data, n):
    d = n - 1
    PPP = data["PPP"]
    rows = all(sum(PPP[al][g] for g in range(d)) == 0 for al in range(d))
    anti = all(sum(PPP[al][(s - al) % d] for al in range(d)) == 0 for s in range(d))
    return rows and anti and sum(data["EPP"]) == 0 and sum(data["PPE"]) == 0


def cabling_check(data, n, r, k):
    """RI/RJ: Phi_k(A_{pq}) = sum over the n pieces of a split leaf of Phi_{k+d}, for every leaf and pair."""
    d = n - 1
    small, big = Phi(data, n, r, k), Phi(data, n, r, k + d)
    for leaf in range(1, k + 1):
        def img(x):
            return [x] if x < leaf else ([leaf + s for s in range(n)] if x == leaf else [x + d])
        for (p, q), v in small.items():
            tot = sum(big[(min(x, y), max(x, y))] for x in img(p) for y in img(q))
            if tot != v:
                return False
    return True


def tau(data, n, r, k):
    return sum(Phi(data, n, r, k).values())


def first_leaf_data(c, n):
    """lamp character lambda(delta_x) = c(res x) pulled back along the first-strand winding map."""
    d = n - 1
    z = [0] * d
    return {"PPP": [[0] * d for _ in range(d)], "EPP": [c[(g + 1) % d] - c[(g + 2) % d] for g in range(d)],
            "PPE": list(z), "PEP": list(z), "EPE": None, "c": list(c)}


def first_leaf(c, n, r):
    data = first_leaf_data(c, n)
    data["EPE"] = c[(r - 1) % len(c)]
    return data


def random_W0(n, r, rng, scale=5):
    """random integer point of W with tau_phi(k) = 0 for all k >= 3, k = r mod d."""
    d = n - 1
    PPP = [[0] * d for _ in range(d)]
    for al in range(1, d):
        for g in range(1, d):
            PPP[al][g] = rng.randint(-scale, scale)
    # fill row 0 / column 0 so that row sums and antidiagonal sums vanish (d-1)^2 free entries
    for al in range(1, d):
        PPP[al][0] = -sum(PPP[al][g] for g in range(1, d))
    # solve for PPP[0][g] from the antidiagonal sum s = g; the s = 0 antidiagonal then vanishes automatically
    for g in range(1, d):
        PPP[0][g] = -sum(PPP[al][(g - al) % d] for al in range(1, d))
    PPP[0][0] = -sum(PPP[0][g] for g in range(1, d))
    EPP = [rng.randint(-scale, scale) for _ in range(d - 1)]
    EPP.append(-sum(EPP))
    PPE = [rng.randint(-scale, scale) for _ in range(d - 1)]
    PPE.append(-sum(PPE))
    PEP = [d * rng.randint(-scale, scale) for _ in range(d)]
    data = {"PPP": [[d * x for x in row] for row in PPP], "EPP": [d * x for x in EPP],
            "PPE": [d * x for x in PPE], "PEP": PEP, "EPE": d * rng.randint(-scale, scale)}
    k0 = 3 if (3 - r) % d == 0 else 3 + ((r - 3) % d)
    t0, t1 = tau(data, n, r, k0), tau(data, n, r, k0 + d)
    slope = Fraction(t1 - t0, d)
    assert slope.denominator == 1
    slope = int(slope)
    data["PEP"] = [x - slope for x in data["PEP"]]
    data["EPE"] -= tau(data, n, r, k0)
    return data


# ---------------------------------------------------------------- main
def main():
    stage = sys.argv[1] if len(sys.argv) > 1 else "main"
    t_start = time.time()
    rng = random.Random(20260916)
    out = {"stage": stage, "primes": list(PRIMES), "sanity": {}, "cases": []}

    # --- sanity 1: Betti numbers of the OS algebra
    for k in range(3, 10):
        assert [len(basis(k, p)) for p in range(k)] == stirling_row(k), k
    out["sanity"]["betti_match_stirling_k3_to_9"] = True

    # --- sanity 2: a /\\ a = 0 at random characters (associativity of the normal form)
    P = PRIMES[0]
    for k in (4, 5, 6):
        a = {(i, j): rng.randint(-9, 9) for j in range(2, k + 1) for i in range(1, j)}
        assert all(dd_zero(k, a, p, P) for p in range(0, k - 2)), k
    out["sanity"]["d_squared_zero_k4_5_6"] = True

    # --- sanity 3: nonzero sum gives an exact complex; KMM circles give H^1 = 1
    a = {(i, j): rng.randint(1, 9) for j in range(2, 6) for i in range(1, j)}
    assert sum(a.values()) % P
    out["sanity"]["k5_positive_character"] = aomoto(5, a, 4, P)
    k4 = lambda d: {(i, j): d.get((i, j), 0) for j in range(2, 5) for i in range(1, j)}
    out["sanity"]["k4_triple_circle_e12_minus_e13"] = aomoto(4, k4({(1, 2): 1, (1, 3): -1}), 3, P)
    out["sanity"]["k4_P4_circle_x1_y2_zm3"] = aomoto(
        4, k4({(1, 2): 1, (3, 4): 1, (1, 3): 2, (2, 4): 2, (1, 4): -3, (2, 3): -3}), 3, P)
    assert out["sanity"]["k5_positive_character"] == [0] * 5
    assert out["sanity"]["k4_triple_circle_e12_minus_e13"][:2] == [0, 1]
    assert out["sanity"]["k4_P4_circle_x1_y2_zm3"][:2] == [0, 1]

    # --- sanity 4: cross-check against the repo's older pure-Python implementation, k = 5
    try:
        old_dir = os.path.join(HERE, "..", "..", "research", "artifacts", "zp-pure-braid-os-resonance-2026-09-13")
        sys.path.insert(0, os.path.abspath(old_dir))
        saved = sys.argv
        sys.argv = [saved[0], "5"]
        import os_resonance as OLD  # noqa: E402
        sys.argv = saved
        agree = []
        for trial in range(3):
            a = {(i, j): rng.randint(-9, 9) for j in range(2, 6) for i in range(1, j)}
            a[(1, 2)] -= sum(a.values())  # zero-sum
            vec = [a[e] % OLD.P for e in OLD.EDGES]
            agree.append(OLD.aomoto_dims(vec) == aomoto(5, a, 4, PRIMES[0]))
        out["sanity"]["crosscheck_old_implementation_k5"] = agree
        assert all(agree)
    except ImportError:
        out["sanity"]["crosscheck_old_implementation_k5"] = "old module not importable"

    # --- sanity 5: Theorem 1 cabling relations and the first-leaf formula
    checks = []
    for n in (3, 4):
        for r in range(1, n + 1):
            for trial in range(2):
                data = random_W0(n, r, rng)
                assert data_constraints_ok(data, n)
                ok = all(cabling_check(data, n, r, k) for k in range(3, 10) if (k - r) % (n - 1) == 0)
                zero = all(tau(data, n, r, k) == 0 for k in range(3, 12) if (k - r) % (n - 1) == 0)
                checks.append(ok and zero)
            c = [rng.randint(-5, 5) for _ in range(n - 1)]
            data = first_leaf(c, n, r)
            ok = all(cabling_check(data, n, r, k) for k in range(3, 10) if (k - r) % (n - 1) == 0)
            for k in range(3, 10):
                if (k - r) % (n - 1):
                    continue
                Ph = Phi(data, n, r, k)
                star = {(1, j): (c[(j - 1) % (n - 1)] - c[j % (n - 1)] if j < k else c[(k - 1) % (n - 1)])
                        for j in range(2, k + 1)}
                ok = ok and all(Ph[e] == star.get(e, 0) for e in Ph) and tau(data, n, r, k) == c[1 % (n - 1)]
            checks.append(ok)
    out["sanity"]["theorem1_cabling_and_first_leaf_formula"] = all(checks)
    assert all(checks)

    # --- cases
    cases = []
    for r in (1, 2):
        cases.append(("n=3 first-leaf star c=(1,0)", 3, r, first_leaf([1, 0], 3, r)))
        cases.append(("n=3 random W_0 point", 3, r, random_W0(3, r, rng)))
    cases.append(("n=3 part-2 example PPP=2(-1)^gamma, PEP=1, EPE=2 (r odd)", 3, 1,
                  {"PPP": [[2, -2], [2, -2]], "EPP": [0, 0], "PPE": [0, 0], "PEP": [1, 1], "EPE": 2}))
    cases.append(("n=3 part-2 example PPP=2(-1)^gamma, PEP=1, EPE=1 (r even)", 3, 2,
                  {"PPP": [[2, -2], [2, -2]], "EPP": [0, 0], "PPE": [0, 0], "PEP": [1, 1], "EPE": 1}))
    for r in (1, 2, 3):
        cases.append(("n=4 first-leaf star c=(1,0,0)", 4, r, first_leaf([1, 0, 0], 4, r)))
        cases.append(("n=4 first-leaf star c=(0,0,1)", 4, r, first_leaf([0, 0, 1], 4, r)))
    if stage == "main":
        budget, primes, ks = {4: 3, 5: 4, 6: 5, 7: 6, 8: 3, 9: 2}, PRIMES, range(4, 10)
    else:  # "deep": one prime, one more degree at k = 8, 9, n = 3 first-leaf star only
        budget, primes, ks = {8: 4, 9: 3}, PRIMES[:1], (8, 9)
        cases = [cs for cs in cases if cs[1] == 3 and "first-leaf" in cs[0]]
    for name, n, r, data in cases:
        for k in ks:
            if (k - r) % (n - 1):
                continue
            a = Phi(data, n, r, k)
            if tau(data, n, r, k) != 0 or not any(a.values()):
                continue
            maxdeg = budget[k]
            t0 = time.time()
            dims = [aomoto(k, a, maxdeg, P) for P in primes]
            support = sorted({x for e, v in a.items() if v for x in e})
            rec = {"case": name, "n": n, "r": r, "k": k, "maxdeg": maxdeg,
                   "Phi_k_nonzero": {f"{i},{j}": v for (i, j), v in a.items() if v},
                   "strands_in_support": len(support),
                   "H_dims_by_prime": {str(P): dd for P, dd in zip(primes, dims)},
                   "seconds": round(time.time() - t0, 2)}
            out["cases"].append(rec)
            print(f"{name:62s} r={r} k={k} H^0..{maxdeg} = {' / '.join(map(str, dims))}  ({rec['seconds']}s)",
                  flush=True)
    out["total_seconds"] = round(time.time() - t_start, 1)
    with open(os.path.join(HERE, "results.json" if stage == "main" else "results_deep.json"), "w") as fh:
        json.dump(out, fh, indent=1)
    print(json.dumps(out["sanity"]), flush=True)
    print("DONE", out["total_seconds"], flush=True)


if __name__ == "__main__":
    main()
