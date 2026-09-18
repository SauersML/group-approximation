"""A Z^3 inside 2V on which log(min brick count) is the l^infinity norm up to O(1).

b_w = baker map supported on the brick [w] x C:  (w a s, t) -> (w s, a t), identity elsewhere.
b_00, b_01, b_1 have disjoint supports, hence commute; g(m,n,p) = b_00^m b_01^n b_1^p.

Lemma (proved in the claim node; checked here by the exact DP for |m|,|n|,|p| <= 3):
    2^max(|m|,|n|,|p|) <= L(g(m,n,p)) <= 2^|m| + 2^|n| + 2^|p|
(the DP finds equality on the right except when m = n = 0).

Part 2: exact certificates that the kernel ||x - y||_inf^beta on a grid {-k..k}^3 is NOT cnd:
integer zero-sum c with Q0 = sum c_i c_j ||x_i - x_j||_inf^beta > 0, verified with the distance
class counts N_d = sum_{||x_i - x_j|| = d} c_i c_j (integers) and Decimal arithmetic (60 digits).

Part 3: explicit finite witness in 2V for F = log L and F = (log L)^(1/2): elements g(lambda x_i)
with a scale lambda for which the interval lower bound from the lemma already gives
sum c_i c_j F(L(g_i^{-1} g_j)) > 0.

Part 2 stores the certificates in zcube_linf_certificates.json and re-verifies them with
integer and Decimal arithmetic only (python3 zcube_obstruction.py --verify does just that).

Usage: python3 zcube_obstruction.py [--verify]
"""
import sys
import itertools
from decimal import Decimal, getcontext

import numpy as np

import lib2v as V
import cnd_census as C

getcontext().prec = 60


def identity_off(w):
    """Identity bricks on the complement of [w] x C."""
    return tuple((w[:i] + ("1" if w[i] == "0" else "0"), "", w[:i] + ("1" if w[i] == "0" else "0"), "")
                 for i in range(len(w)))


def baker_on(w):
    return ((w + "0", "", w, "0"), (w + "1", "", w, "1")) + identity_off(w)


def power(g, k):
    e = V.ID
    base = g if k >= 0 else V.inverse(g)
    for _ in range(abs(k)):
        e = V.reduce_greedy(V.compose(e, base))
    return e


B = {w: baker_on(w) for w in ("00", "01", "1")}


def g_of(m, n, p):
    return V.reduce_greedy(V.compose(V.compose(power(B["00"], m), power(B["01"], n)), power(B["1"], p)))


def part1():
    for w in B:
        V.check(B[w])
    assert V.is_identity(V.compose(V.compose(B["00"], B["1"]), V.inverse(V.compose(B["1"], B["00"]))))
    bad = eq = 0
    for m, n, p in itertools.product(range(-3, 4), repeat=3):
        g = g_of(m, n, p)
        V.check(g)
        L = V.min_bricks(g)
        lo, hi = 2 ** max(abs(m), abs(n), abs(p)), 2 ** abs(m) + 2 ** abs(n) + 2 ** abs(p)
        if not (lo <= L <= hi):
            bad += 1
            print("  BOUND FAILURE", (m, n, p), "L", L, "bounds", lo, hi)
        eq += (L == hi)
    print(f"part 1: 343 elements g(m,n,p), |.|<=3: bound failures {bad}; "
          f"L equals the upper bound in {eq} cases (the others have m = n = 0, where [0]xC is one brick)")


def grid_witness(k, beta, scale=10 ** 6):
    P = np.array(list(itertools.product(range(-k, k + 1), repeat=3)))
    D = np.abs(P[:, None, :] - P[None, :, :]).max(-1)
    lam, vec = C.top_zero_sum(D.astype(float) ** beta)
    c = [int(round(scale * x)) for x in vec]
    i0 = max(range(len(c)), key=lambda i: abs(c[i]))
    c[i0] -= sum(c)
    ca = np.array(c, dtype=object)
    N = {}
    for d in range(1, 2 * k + 1):
        mask = (D == d)
        N[d] = int(sum(ca[i] * sum(ca[j] for j in np.nonzero(mask[i])[0]) for i in range(len(c))))
    Q0 = sum(Decimal(N[d]) * Decimal(d) ** Decimal(beta) for d in N)
    return P, D, c, N, Q0, lam


CERT_FILE = "zcube_linf_certificates.json"


def verify_certificates(path=CERT_FILE):
    """Re-verify the stored certificates with integers and Decimal only (no numpy, no eigensolver)."""
    import json
    with open(path) as fh:
        certs = json.load(fh)
    for cert in certs:
        k, beta, c = cert["k"], Decimal(cert["beta"]), cert["c"]
        pts = list(itertools.product(range(-k, k + 1), repeat=3))
        assert len(pts) == len(c) and sum(c) == 0
        N = {}
        for i, x in enumerate(pts):
            for j, y in enumerate(pts):
                d = max(abs(a - b) for a, b in zip(x, y))
                if d:
                    N[d] = N.get(d, 0) + c[i] * c[j]
        Q0 = sum(Decimal(N[d]) * Decimal(d) ** beta for d in N)
        print(f"verify: k={k} beta={cert['beta']} points={len(pts)} Q0={Q0:.12e} "
              f"{'CERTIFIED' if Q0 > Decimal(10) ** -30 else 'FAILED'}")


def part2():
    import json
    out = {}
    certs = []
    for k, beta in ((1, 1.0), (2, 0.5), (5, 0.25)):
        P, D, c, N, Q0, lam = grid_witness(k, beta)
        certs.append({"k": k, "beta": str(beta), "points": "itertools.product(range(-k, k+1), repeat=3)",
                      "c": c, "N_d": {str(d): N[d] for d in N}, "Q0": f"{Q0:.20e}"})
        ok = Q0 > Decimal(10) ** -40
        print(f"part 2: grid k={k} ({len(c)} pts) beta={beta}: float lambda={lam:.4f}  "
              f"N_d={N}  sum c^2={sum(x * x for x in c)}  Q0={Q0:.10e}  "
              f"{'CERTIFIED' if ok else 'NOT CERTIFIED'}")
        out[(k, beta)] = (P, D, c, N, Q0)
    with open(CERT_FILE, "w") as fh:
        json.dump(certs, fh)
    verify_certificates()
    return out


def part3(wit):
    ln2, ln3 = Decimal(2).ln(), Decimal(3).ln()
    for (k, beta) in ((1, 1.0), (2, 0.5)):
        P, D, c, N, Q0 = wit[(k, beta)]
        b = Decimal(beta)
        for lam in range(1, 200):
            # c_i c_j > 0 pairs: use lower bound (lam d ln2)^beta; < 0 pairs: upper (lam d ln2 + ln3)^beta.
            # Separate positive and negative parts of each distance class.
            if lam == 1:
                cache = {}
                for d in N:
                    mask = (D == d)
                    s_pos = s_neg = 0
                    for i in range(len(c)):
                        for j in np.nonzero(mask[i])[0]:
                            v = c[i] * c[j]
                            if v > 0:
                                s_pos += v
                            else:
                                s_neg += v
                    cache[d] = (s_pos, s_neg)
                part3.cache = cache
            cache = part3.cache
            Q = Decimal(0)
            for d, (s_pos, s_neg) in cache.items():
                Q += Decimal(s_pos) * (lam * d * ln2) ** b + Decimal(s_neg) * (lam * d * ln2 + ln3) ** b
            if Q > 0:
                print(f"part 3: F=(log L)^{beta}: grid k={k}, scale lambda={lam}: interval lower bound "
                      f"sum c_i c_j F(L(g_i^-1 g_j)) >= {Q:.6e} > 0  CERTIFIED "
                      f"(elements g(lambda x), x in {{-{k}..{k}}}^3, exponents up to {lam * k})")
                break


FIVE = [(-1, 0, 0), (-1, 0, 1), (0, -1, 1), (0, 1, 1), (1, 0, 1)]
FIVE_C = [-2, -2, 3, 3, -2]


def part4():
    """Five-point witness, pure integer arithmetic.

    sum_{i,j} c_i c_j ||x_i - x_j||_inf = 4 > 0.  With g_i = g(lam x_i) the lemma gives
    2^(lam d) <= L(g_i^-1 g_j) <= 3 * 2^(lam d), d = ||x_j - x_i||_inf, so
    prod_{i != j} L_ij^(c_i c_j) >= prod_{c_i c_j > 0} 2^(lam d c_i c_j) / prod_{c_i c_j < 0} (3 2^(lam d))^|c_i c_j|
    and sum c_i c_j log L_ij > 0 as soon as that integer ratio exceeds 1.
    """
    n = len(FIVE)
    d = [[max(abs(a - b) for a, b in zip(FIVE[i], FIVE[j])) for j in range(n)] for i in range(n)]
    assert sum(FIVE_C) == 0
    Q0 = sum(FIVE_C[i] * FIVE_C[j] * d[i][j] for i in range(n) for j in range(n))
    print(f"part 4: five points {FIVE}, c = {FIVE_C}, l^inf distances {d}, Q0 = {Q0}")
    for lam in range(1, 100):
        num_exp2 = den_exp2 = den_exp3 = 0
        for i in range(n):
            for j in range(n):
                if i == j:
                    continue
                e = FIVE_C[i] * FIVE_C[j]
                if e > 0:
                    num_exp2 += lam * d[i][j] * e
                else:
                    den_exp2 += lam * d[i][j] * (-e)
                    den_exp3 += -e
        if 2 ** num_exp2 > 2 ** den_exp2 * 3 ** den_exp3:
            print(f"part 4: lambda={lam}: 2^{num_exp2} > 2^{den_exp2} * 3^{den_exp3}, so "
                  f"sum c_i c_j log L(g_i^-1 g_j) > 0 for g_i = b_00^(lam m) b_01^(lam n) b_1^(lam p)  CERTIFIED")
            break
    # sanity at small scale with the exact DP (lam = 1, 2): the exact quadratic form
    import math
    for lam in (1, 2):
        els = [g_of(*(lam * t for t in x)) for x in FIVE]
        Lm = [[V.min_bricks(V.reduce_greedy(V.compose(V.inverse(els[i]), els[j]))) for j in range(n)]
              for i in range(n)]
        q = sum(FIVE_C[i] * FIVE_C[j] * math.log(Lm[i][j]) for i in range(n) for j in range(n))
        print(f"part 4 sanity: lambda={lam} exact L matrix {Lm}, float sum c_i c_j log L = {q:+.4f}")


if __name__ == "__main__":
    if "--verify" in sys.argv:
        verify_certificates()
        sys.exit(0)
    part1()
    w = part2()
    part3(w)
    part4()
