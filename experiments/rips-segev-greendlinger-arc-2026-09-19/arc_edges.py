"""Lemma G of rips-segev-ba-layered-no-left-annihilator-proof.

A face boundary has beta_M b-runs (1 or 2 edges each) and E >= 42 b-edges.  An exterior
arc s has |omega(s)|_* > (5/8)(2 beta_M), so beta_s >= floor(5 beta_M/8 - 1/2) + 1 b-syllables,
and rho_s >= max(0, 40 - 2 beta_M + beta_s) two-edge syllables.  E_s = beta_s + rho_s.
We minimise the lower bound over beta_M and every admissible beta_s (beta_s <= beta_M + 1).
"""
from fractions import Fraction as Fr

best = None
for bM in range(21, 201):
    lo = int(Fr(5 * bM, 8) - Fr(1, 2)) + 1      # floor(5bM/8 - 1/2) + 1, argument > 0
    for bs in range(lo, bM + 2):
        # syllable-length check: 2 bs + 1 >= |omega(s)|_* > 5 bM / 4
        assert 2 * bs + 1 > Fr(5 * bM, 4)
        Es = bs + max(0, 40 - 2 * bM + bs)
        if best is None or Es < best[0]:
            best = (Es, bM, bs)
    print(bM, lo, lo + max(0, 40 - 2 * bM + lo))
print("min E_s =", best[0], "at beta_M =", best[1], "beta_s =", best[2])
assert best[0] == 18
