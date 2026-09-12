---
rg: 2
id: leavitt-semisimple-torsion-conjugacy-proof
kind: route
title: Primary decomposition, separable base change and Bergman's projective monoid conjugate semisimple torsion units with equal support
target: leavitt-semisimple-torsion-units-conjugate-iff-same-support
requires:
  - binary-leavitt-nonzero-projectives-are-free
artifacts:
  - research/artifacts/ternary-minus-one-gate-outside-signed-thompson-2026-09-12.md
---

Artifact Section 2, Theorem 2.1.

1. **Necessity.** Conjugation carries `e_q(g)` to `e_q(ugu^-1)`, so it preserves the support.
2. **Decomposition.** `x^m - 1` is separable, so the Chinese remainder theorem gives orthogonal idempotents
   `e_q(g) in K[g]` summing to 1, and `R_R = ⊕ e_q(g)R`.
3. **Module structure.** `P_q = e_q(g)R` is a right `R_q = K_q ⊗_K R`-module, with `K_q` acting by left
   multiplication by `g`, which commutes with the right `R`-action.
   - `R_q ≅ L_(K_q)(1,2)`.
   - `P_q` is a finitely generated projective `R`-module, being a summand of `R_R`.
   - `R_q` is a separable `R`-algebra, because `K_q/K` is separable. So `P_q` is projective over `R_q`.
4. **Freeness.** Every nonzero `P_q` is `≅ R_q` by the required node over the field `K_q`. The same holds for `P'_q`.
5. **Conjugation.** Choose `R_q`-isomorphisms `φ_q : P_q -> P'_q`. They are right `R`-linear and satisfy
   `φ_q(gp) = g'φ_q(p)`. So `φ = ⊕ φ_q` is an automorphism of `R_R` with `φ(gp) = g'φ(p)`. Then `φ` is left
   multiplication by `u = φ(1) in R^x`, and `ug = g'u`.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 27.2 (main theorem; the order-8 corollary negation-closure claim not re-derived) of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
