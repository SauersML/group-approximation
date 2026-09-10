#!/usr/bin/env python3
"""sp-design deliverable 3, the ParityData-shaped statement (the form sp-evenside lands).

Structure (the general-p analogue of CharClass/ParityEven.lean's `ParityData`):
  gamma_k(W) = iota(a_k) + z * iota(b_k),  z of weight n+1, z^2 = 0,
  a_k of weight k in H^*(Y),  b_k of weight k-(n+1).
Hypotheses:
  (A)  a_q = 0 unless p | q,  a_0 = 1                      [Frobenius, from p | d_j]
  (I)  P^i(b_k) = 0 whenever i > k - (n+1)                  [instability]
  (W)  P^i(gamma_{i+1}) = Q_i(gamma), Q_i homogeneous of weight ip+1,
       Q_i = gamma_{ip+1} + (products of at least two gammas)  [diagonal Wu]
Conclusion:
  b_N = 0 for every N = 1 mod p;   hence gamma_r(W) = 0 when r = 1 mod p.

This script checks, for the ACTUAL universal Wu polynomials E_{i+1} computed by Newton's
identities, that (W) holds in the claimed shape and that the z-part of the diagonal
relation is exactly
   0 = b_{ip+1} + sum over terms whose b-index is = 1 mod p and <= ip+1-p .
"""
import sys
sys.path.insert(0, ".")
from itertools import product
from lix_modp_uniform_check import phi_universal, comb


def run(n, p, d, verbose=True):
    l = len(d); m = sum(d); r = n + 1 + m
    assert all(x % p == 0 for x in d), "need p | d_j"
    # a_q = coefficient of gamma(V) in weight q, as a plain polynomial in h (truncated)
    monos = [tuple(x) for x in product(*[range(di + 1) for di in d])]
    def gV_coeff(mo):
        c = 1
        for i, di in enumerate(d):
            c = c * comb(di, mo[i])
        return c % p
    a_supp = {q for q in range(m + 1) if any(gV_coeff(mo) for mo in monos if sum(mo) == q)}
    fails = []
    # (A)
    for q in a_supp:
        if q % p:
            fails.append(f"(A) a_{q} != 0 but p does not divide {q}")
    if gV_coeff(tuple([0] * l)) != 1:
        fails.append("(A) a_0 != 1")
    Es = phi_universal(r, p)
    imax = (r - 1) // p
    kills = []
    for i in range(0, imax + 1):
        N = i * p + 1
        if N > r:
            break
        # weight-N part of E_{i+1}
        comp = {}
        for exps, c in Es[i + 1].items():
            w = sum((j + 1) * x for j, x in enumerate(exps))
            if w != N:
                continue
            lam = tuple(sorted([j + 1 for j, x in enumerate(exps) for _ in range(x)], reverse=True))
            comp[lam] = c
        # (W) shape
        if comp.get((N,), 0) % p != 1:
            fails.append(f"(W) i={i}: coefficient of gamma_{N} is {comp.get((N,),0)}, not 1")
        # (I): weight of b_{i+1} is i+1-(n+1) = i-n < i, so P^i kills it
        if not (i - n < i):
            fails.append(f"(I) i={i}: instability does not apply")
        # z-part: replace one gamma_alpha by b_alpha, the rest by a
        live = []
        for lam, c in comp.items():
            for t in range(len(lam)):
                others = lam[:t] + lam[t + 1:]
                if any(q not in a_supp for q in others):
                    continue                      # that product of a's is zero
                live.append((lam[t], others, c))
        for alpha, others, c in live:
            if alpha % p != 1 % p:
                fails.append(f"(z) i={i}: surviving b-index {alpha} is not 1 mod p")
            if others and alpha > N - p:
                fails.append(f"(z) i={i}: decomposable term has b-index {alpha} > {N-p}")
            if not others and alpha != N:
                fails.append(f"(z) i={i}: linear term with index {alpha} != {N}")
        kills.append(N)
    # conclusion
    if (r - 1) % p:
        fails.append(f"conclusion: r-1 = {r-1} is not 0 mod p, so gamma_r is not reached")
    if r not in kills and (r - 1) % p == 0:
        fails.append(f"conclusion: r={r} is not among the killed indices {kills}")
    st = "OK" if not fails else "FAIL: " + "; ".join(sorted(set(fails))[:4])
    if verbose:
        print(f"n={n} p={p} d={list(d)} m={m} r={r}: {st}   "
              f"b_N killed for N in {kills[:6]}{'...' if len(kills)>6 else ''}", flush=True)
    return fails


if __name__ == "__main__":
    cases = []
    for n, p in [(2,2),(4,2),(6,2),(6,3),(3,3),(9,3),(5,5),(10,5),(15,5),(7,7),(14,7),(11,11),
                 (12,2),(12,3),(30,2),(30,3),(30,5)]:
        for stages in (1, 2, 3):
            d = [n * 2**j for j in range(stages)]
            if sum(d) + n + 1 > 46:      # keep the universal Wu computation feasible
                continue
            cases.append((n, p, d))
    if len(sys.argv) > 1:
        cases = [eval(a) for a in sys.argv[1:]]
    bad = 0
    for (n, p, d) in cases:
        try:
            f = run(n, p, d)
        except Exception as ex:
            print(f"n={n} p={p} d={d}: EXC {type(ex).__name__}: {ex}", flush=True); bad += 1; continue
        if f: bad += 1
    print()
    print("cases with a failure:", bad, "of", len(cases))
