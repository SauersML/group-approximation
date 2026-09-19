---
rg: 2
id: leavitt-unit-span-surjection-proof
kind: route
title: Square-zero corners are differences of units; four corners rebuild the element
target: leavitt-unit-group-algebra-surjects-onto-leavitt
requires: []
artifacts:
  - GroupApproximation/Leavitt/UnitAdditiveSpan.lean
  - research/artifacts/kaplansky-direct-finiteness-audit-2026-08-17.md
---

## Direct proof, machine-checked

`GroupApproximation/Leavitt/UnitAdditiveSpan.lean`, four steps.

1. **Square-zero elements are differences of units.**  If `x^2 = 0` then
   `1 + x` is a unit with inverse `1 - x` (`squareZeroUnit`), so
   `x = (1+x) - 1` lies in `unitAdditiveSpan A`.

2. **Products of two square-zero elements too.**
   `xy = (1+x)(1+y) - 1 - x - y` (`squareZero_mul_mem_unitAdditiveSpan`), and
   every term on the right is already in the span by step 1.

3. **All four Leavitt corners are covered.**  `t_1s_0 = t_0s_1 = 0` makes
   `s_0 a t_1` and `s_1 a t_0` square-zero; the diagonal corners are products
   of two such, via `s_0 a t_0 = (s_0 a t_1)(s_1 t_0)` and
   `s_1 a t_1 = (s_1 a t_0)(s_0 t_1)`, each identity being one application of
   `t_1s_1 = 1`, resp. `t_0s_0 = 1`.

4. **The corners sum to the element.**  Expanding
   `a = 1 a 1 = (s_0t_0 + s_1t_1) a (s_0t_0 + s_1t_1)` gives exactly those
   four corner terms, so `unitAdditiveSpan A = top`
   (`unitAdditiveSpan_eq_top`).

For the surjection, take `A = R = L_(F_2)(1,2)`.  An additive combination of
units over `Z` becomes an `F_2`-combination because `2 = 0`, and the
`F_2`-algebra map `F_2[R^x] -> R` determined by `[u] |-> u` on the basis is
unital by construction and now hits every element.
