---
rg: 2
id: rank-three-stable-fivefold-commutator-two-primary
kind: claim
title: The stable fivefold commutator map of U(3) has 2-power order, and 2-locally it is the SU(3) map composed with the projection U(3) -> SU(3)
distinct_from:
  rank-two-trapping-blind-to-depth-four-brackets: That shows the stable fivefold commutator of U(2) is null at every prime; this shows the U(3) map is null at every odd prime, including 3, and reduces the 2-primary part to SU(3).
---

Let G = U(3), cbar_5: G^{∧5} -> SU(3) the nested commutator
(g_4, g_3, g_2, g_1, h) -> [g_4, [g_3, [g_2, [g_1, h]]]], and
s_5 = Sigma^∞ cbar_5.

(a) For every odd prime p, s_5 localized at p is null.
(b) s_5 has finite order, a power of 2. So for every generalized homology
    theory E, 2^k·(cbar_5)_* = 0 on reduced E-homology for some k. Every
    trapped class of a fivefold commutator seed witness in protected rank
    three, for every tangential structure, has 2-power order.
(c) Let pr: U(3) -> SU(3) be the second coordinate of the homeomorphism
    S^1 x SU(3) -> U(3), (z, g) -> diag(z, 1, 1)·g. After localization at 2,
    s_5 ≃ Sigma^∞ cbar_5^{SU(3)} o (Sigma^∞ pr)^{∧5}. Stably
    Sigma^∞ SU(3) ≃ Sigma CP^2 ∨ S^8, with Sigma CP^2 = S^3 ∪_eta e^5.

So a class-five input in protected rank three is a 2-primary statement about
SU(3). This closes the prime 3 for U(3)-valued seeds, which the class-five
root had left unchecked: Kaji–Kishimoto covers simply connected p-regular
groups, and U(3) is not simply connected.

The same count shows that the p-primary parts vanish for p >= 5 already on
the fourfold map. At p = 3 the count for the fourfold map leaves
alpha_1·beta_1^2 in stem 23 as a possible value. That case is not settled
here.

Proof: rank-three-fivefold-commutator-odd-primes-proof. Complete argument,
using standard values of the 3- and 5-primary stable stems through stem 26
and Toda's relation alpha_1·beta_1^3 = 0, recalled and not re-verified from
the source in this lane. Not independently reviewed.
