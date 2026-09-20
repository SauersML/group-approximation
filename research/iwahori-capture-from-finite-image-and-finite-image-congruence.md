---
rg: 2
id: iwahori-capture-from-finite-image-and-finite-image-congruence
kind: route
title: Replace the first vertex by a nearby finite-image representation, pad the second vertex, and apply the finite-image half
target: iwahori-one-vertex-congruence-capture
requires:
  - iwahori-vertex-finite-image-capture
  - iwahori-finite-image-vertex-congruence-capture
  - flexible-hs-metric-controls-words-and-padding
---

**Decomposition.** One-vertex congruence capture is equivalent to the
conjunction of
* **(FI)** `iwahori-vertex-finite-image-capture`, the infinite-image half,
  and
* **(NC)** `iwahori-finite-image-vertex-congruence-capture`, the
  non-congruence finite-image half.

The two halves are independently failable. (FI) concerns only
infinite-image mass and is silent on non-congruence finite quotients. (NC)
assumes finite image and is silent on infinite-image mass.

**Converse (trivial).** Congruence representations have finite image, so
capture gives (FI). (NC) is a special case of capture.

**Proof that (FI) and (NC) give capture.** This is the replacement argument
of Step 6 of `iwahori-congruence-capture-transfer-proof`, with "finite
image" in place of "congruence". Let `pi_n` be exact pairs on `C^(d_n)` with
`eps_n := def(pi_n) -> 0`. Let `L_+` be the largest `S_C`-word length of an
element of `S_+`.

1. The finite-image class is closed under adding trivial summands. So by
   `flexible-hs-metric-controls-words-and-padding` (`A <= A_up <= 2A`) there
   is an exact finite-image `rho_n` on `C^(D_n)`, with `D_n >= d_n` and
   `b_n := d_2(pi_(n,+), rho_n) <= 2 A_fin(pi_(n,+)) + 1/n`. By (FI),
   `b_n -> 0`.
2. Put `pi^1_n = (rho_n, pi_(n,-) (+) 1_(D_n - d_n))`. This is an exact pair
   whose first vertex has finite image. The same lemma gives
   `sqrt((D_n - d_n)/D_n) <= b_n`.
3. As in Step 6.3 there, `def(pi^1_n) <= eps_n + (L_+ + 1) b_n -> 0`.
4. By (NC), `A_+(pi^1_n) -> 0`. The generalized `d_2` is a metric, so
   `A_+(pi_n) <= d_2(pi_(n,+), rho_n) + A_+(pi^1_n) <= b_n + A_+(pi^1_n) -> 0`.

The quantitative form is the same: if (FI) holds with modulus `f` and (NC)
with a monotone modulus `g`, then `A_+ <= 2f(eps) + g(eps + 2(L_+ + 1) f(eps))`.
