---
rg: 2
id: full-group-algebra-to-steinberg-algebra-not-injective-proof
kind: route
title: Four piecewise bisections cancel on each piece, while the four group elements are distinct
target: full-group-algebra-to-steinberg-algebra-not-injective
requires:
  - full-group-units-embed-in-steinberg-algebras
---

Put `g_(ij) = alpha_i ⊔ beta_j` for `i, j in {0, 1}`, with `alpha_0 = alpha`,
`alpha_1 = alpha'`, `beta_0 = beta`, `beta_1 = beta'`.

1. **They are full bisections.** Each `g_(ij)` is a compact open bisection, as
   a union of bisections with disjoint sources and disjoint ranges. Its source and
   range are `U ⊔ W = G^(0)`, so `g_(ij) in [[G]]`.
2. **They are distinct.** `g_(ij) = g_(i'j')` forces `alpha_i = alpha_(i')` by
   restricting to arrows with source in `U`, and `beta_j = beta_(j')` by
   restricting to `W`. So `i = i'` and `j = j'`.
3. **The images cancel.** Indicator functions add over disjoint unions:
   `1_(g_(ij)) = 1_(alpha_i) + 1_(beta_j)`. Hence

   ```text
   1_(g_00) - 1_(g_01) - 1_(g_10) + 1_(g_11)
     = (1_a + 1_b) - (1_a + 1_b') - (1_a' + 1_b) + (1_a' + 1_b') = 0.
   ```

   Here `a, a', b, b'` abbreviate `alpha, alpha', beta, beta'`.
4. **The group-algebra element is nonzero.** `g_00 - g_01 - g_10 + g_11` has
   four distinct basis elements with coefficients `±1 != 0` in `R[ [[G]] ]`.
5. **The Cuntz groupoid qualifies.** For `U = [0]`:
   - `alpha` is the identity bisection of `U`;
   - `alpha'` swaps the cylinders `[00]` and `[01]` by the prefix exchange
     `00w <-> 01w`, a compact open bisection with source and range `U`.

   The same construction on `W = [1]` gives `beta`, `beta'`.
