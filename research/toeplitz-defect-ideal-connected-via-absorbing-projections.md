---
rg: 2
id: toeplitz-defect-ideal-connected-via-absorbing-projections
kind: route
title: DEAD. Compress each unitary of 1 + J under an absorbing projection with properly infinite full complement
target: toeplitz-defect-ideal-unitization-k1-injective
requires: []
---

**The approach.**
- Suppose that for every `x ∈ J` and `ε > 0` there is a projection `q ∈ B_J` with `||qx − x|| < ε`,
  `||xq − x|| < ε`, and `1 − q` properly infinite and full.
- For `u = 1 + x` one would perturb `q u q + (1 − q)` to a unitary `u'` of `1 + qJq` close to `u`, so
  `u ~_h u'`.
- Halve `1 − q` into properly infinite full `g_1, g_2`, and put `p = q + g_1`. Then `p` commutes with
  `u'`, and `p`, `1 − p` are properly infinite and full.
- `K_1(B_J) = 0`, so `brr-commutator-criterion-null-unitary` makes `u'` null in `B_J`.
  `o2-quotient-extension-ideal-k1-injective-iff-algebra` then gives `u ∈ U_0(J~)`.

**Dead.** `toeplitz-defect-ideal-absorbers-have-nonfull-complement`: for `u_0 = exp(ik_0)` with
`π(u_0) = −1` in the O_3 quotient, every projection `q ∈ B_J` with `||qx_0 − x_0|| < 2` has `π(q) = 1`,
so its complement is not full.

The implication itself is correct; its hypothesis fails. The variant restricted to
`1 + (J ∩ ker π)`, for all unital quotients π of `J` at once, is not covered by the obstruction.
