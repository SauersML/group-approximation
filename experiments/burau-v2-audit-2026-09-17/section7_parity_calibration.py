"""Calibrate the graph's parity lemma against arXiv:2607.05283v2, Section 7.

The preprint lists three unsimplified Moody polynomials, each as a sequence of
signed monomials in the order the arc meets alpha (v2 pp. 25-26):
  M_Phi        (arc of Fig 7.1; stated NOT to satisfy parity; has a cancellation)
  M_{Phi.Gamma} (Fig 7.3; stated to satisfy parity)
  M_Gamma      (Fig 7.4; stated to satisfy parity; 20 terms)
Parity lemma (artifact zp-burau-parity-t-minus-one-obstruction-2026-09-16, sec 6):
a transverse representative is parity-clean iff |M(-1)| equals its number of
crossings with alpha, i.e. iff every term eps_i t^{k_i} has eps_i (-1)^{k_i}
of one common sign.  Also checks the preprint's simplified sums.
Exact integer arithmetic; no inputs.
"""
from collections import Counter

# (sign, exponent) in the order printed in v2, Section 7.
M_PHI = [(1, 0), (1, 2), (1, 4), (-1, 3), (-1, 1), (1, -3), (1, -1), (1, 1)]
M_PHI_GAMMA = [(1, 0), (1, 2), (1, 4), (-1, 3), (-1, 1), (1, -4), (1, -2), (1, 0)]
M_GAMMA = [(-1, 0), (-1, 2), (1, 1), (1, -1), (-1, 0), (-1, 2), (1, 3), (1, 1),
           (1, -1), (-1, -2), (-1, 0), (1, -1), (1, -3), (-1, -2), (-1, 0),
           (1, 1), (1, -1), (1, -3), (-1, -2), (-1, 0)]

# Simplified forms printed in v2 (exponent -> coefficient).
S_PHI = {0: 1, 2: 1, 4: 1, 3: -1, -3: 1, -1: 1}
S_PHI_GAMMA = {0: 2, 2: 1, 4: 1, 3: -1, 1: -1, -4: 1, -2: 1}
S_GAMMA = {-3: 2, -2: -3, -1: 4, 0: -5, 1: 3, 2: -2, 3: 1}


def simplify(terms):
    c = Counter()
    for s, k in terms:
        c[k] += s
    return {k: v for k, v in c.items() if v}


def at_minus_one(terms):
    return sum(s * (-1) ** (k % 2) for s, k in terms)


def parity_clean(terms):
    return len({s * (-1) ** (k % 2) for s, k in terms}) == 1


def no_cancellation(terms):
    seen = {}
    for s, k in terms:
        if seen.setdefault(k, s) != s:
            return False
    return True


ok = True
for name, terms, simp, claimed_parity in [
        ("M_Phi", M_PHI, S_PHI, False),
        ("M_PhiGamma", M_PHI_GAMMA, S_PHI_GAMMA, True),
        ("M_Gamma", M_GAMMA, S_GAMMA, True)]:
    m1 = at_minus_one(terms)
    row = dict(terms=len(terms), M_at_minus_1=m1, parity_clean=parity_clean(terms),
               no_cancellation=no_cancellation(terms),
               simplified_matches=(simplify(terms) == simp))
    print(name, row)
    ok &= row["simplified_matches"]
    ok &= (row["parity_clean"] == claimed_parity)
    ok &= (row["parity_clean"] == (abs(m1) == len(terms)))
print("PREPRINT SECTION 7 CONSISTENT WITH PARITY LEMMA:", ok)
