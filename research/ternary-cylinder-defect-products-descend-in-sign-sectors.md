---
rg: 2
id: ternary-cylinder-defect-products-descend-in-sign-sectors
kind: claim
title: Products of disjoint cylinder defects in anti-central ternary rank functions shrink by two thirds and grow at least the gap times their anti-central sign sector
distinct_from:
  nested-two-root-defect-pieces-decay-geometrically-both-ways: that is the characteristic-two two-sided descent on fixed-point-free rank ultraproduct models, whose lower bound uses range corners and globality; this is the characteristic-three descent for abstract Sylvester rank functions, whose lower bound holds only on the sign sector where the complement is anti-central.
  near-minimal-defect-models-have-multiplicative-cylinder-defects: that pins the characteristic-two descent ratio at near-minimal defect through kernel corners; this gives no such pinning, because the ternary lower bound is sector-limited.
artifacts:
  - research/artifacts/char-three-defect-gap-and-descent-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w5-c3-descent`; independent re-derivation requested from `w4-vf-gate`) by
`ternary-cylinder-defect-descent-proof`.

**Setting.** As in `ternary-anti-central-two-root-defect-has-a-uniform-gap`, with `c_3` its attained minimum.
* `N` is an anti-central Sylvester matrix rank function on `F_3[G]`, where `G = L_(F_3)(1,2)^x`.
* `A_1, ..., A_k, B` are pairwise disjoint nonempty proper cylinders with proper union.
* `P_k = D_(A_1) ... D_(A_k)`, `f(k) = N(P_k)` and `h_k = N(Q_B P_k)`.
* `R_+` is the sum of the joint sign idempotents of `[tau_(A_1)], ..., [tau_(A_k)]` with an even number of minus
  signs.

**Statement.**
1. **Upper.** `f(k+1) <= (2/3) f(k)`. This holds for every Sylvester rank function on `F_3[G]`.
2. **Lower.** `f(k+1) >= N(D_B Q_B P_k) >= c_3 h_k`.
3. **Sector half.** `h_k >= N(R_+ P_k)/2`, with equality sector by sector on the sectors of `R_+`.
4. **Positivity.** `f(k+1) > 0` iff `h_k > 0`.

All four quantities depend only on `k`.

**Scope.** Abstract. No images, range idempotents or annihilators are used, only commuting compressions and the
Frobenius inequality (`sylvester-rank-functions-compress-along-commuting-elements`). So the statement also holds
in the matricial scope.

**Where it stops.** The characteristic-two lower bound `f(k+1) >= c_* f(k)` does not port.
* **Pullback.** The pullback of an anti-central function along `iota_B` is anti-central only on `Q_B`. Its
  `(1 - Q_B)`-part is a model of `PG`, and no gap is known for it.
* **Odd sectors.** On sign sectors with an odd number of minus signs, the complement's reflections act through
  `PG`, and the half split fails.
* **What would fix it.** If `N(R_+ P_k) >= beta f(k)` held uniformly, the descent would be two-sided, with ratio
  in `[beta c_3/2, 2/3]`.
