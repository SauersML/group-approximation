---
rg: 2
id: fpbs-quotient-spectral-dt-certificates-are-subgroup-blind-proof
kind: route
title: Sum the exploration inequality over H on the Schreier space, compare return probabilities by a faithful trace, and lift test vectors along Følner sets
target: fpbs-quotient-spectral-dt-certificates-are-subgroup-blind
requires: []
artifacts:
  - research/artifacts/fpbs-spectral-dt-certificate-2026-09-17.md
---

The complete proof is in the artifact. It uses no import.

1. **Theorem B.**
   * Sum Lemma 2.1 over `y in H`. This gives
     `sigma <= f + sum_g nu(g) sigma(. g)` with `f(x) = |xS ∩ H|`.
   * `f` is left `H`-invariant, bounded by `|S|`, and supported on at most
     `|S|` cosets. So the main terms are at most `|S|^2 ||R_H^k||`.
   * The finite-volume remainder is at most
     `|Lambda ∩ H| |H\H Lambda| ||R_H^m||`, which tends to 0.
   * Openness follows as in Corollary 3.1.
2. **Lemma 5.1.** For `b = rho(f^* * f)` on `l2(Gamma)`,
   `||b|| = lim <b^k delta_e, delta_e>^(1/k)`. Otherwise a positive `g(b)`
   annihilates the cyclic vector `delta_e` for the commuting left translations.
3. **Proposition C.1.** `c^{*k}(e) <= c^{*k}(H)`, which is a diagonal matrix
   coefficient on `l2(H\Gamma)`.
4. **Proposition C.2.** Lift `phi(t) 1_F(h)` along a transversal. Only finitely
   many cocycle values `c(t,g)` occur, and right Følner sets of `H` make the
   form almost exact.
5. **Corollary 5.2.** Apply C to `nu^{*k}` and use Gelfand's formula.
