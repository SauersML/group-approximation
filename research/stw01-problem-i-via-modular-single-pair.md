---
rg: 2
id: stw01-problem-i-via-modular-single-pair
kind: route
title: Settle Problem I by additivity of one fixed pair in C*(PSL_2(Z))
target: stw99-problem-i-quasitraces-are-traces
requires:
  - stw01-modular-single-pair-quasitrace-additivity
---

If every bounded 2-quasitrace on `C*(PSL_2(Z)) = C^3 * C^2` is additive on the one pair
`h = e_1 p e_1`, `k = e_1 p e_2 p e_1`, then Problem I holds. Full proof:
`research/artifacts/stw01-modular-single-pair-test-2026-09-12.md`, Section 2.

Outline.
1. **Steps 0-3.** If Problem I fails, the reviewed Steps 0-3 give a type `II_1`
   AW*-factor `M`, its canonical quasitrace `tau`, a projection `q`, `beta > 0` and a
   finite-spectrum `y = sum gamma_i e_i >= 0` with `D(y, beta q) != 0`. Also
   `gamma_1 > 0`.
2. **Tune the rescaling.** For `eps in (0, 1/(2 gamma_1))` put
   `a_eps = (1/2) 1 + eps y` and `m(eps) = min_i lambda_i (1 - lambda_i)`. The quotient
   `m(eps)/eps` runs continuously from `+infinity` to `0`, so some `eps` gives
   `m(eps) = eps beta`. Additivity on commuting pairs and homogeneity give
   `tau(a + mq) - tau(a) - tau(mq) = eps D(y, beta q) != 0`.
3. **Dilate and pull back.** The three-block dilation (Step 4', reviewed PASS in the
   artifact) gives a projection `r in M_3(M)` with `f_1 r f_1 = a (+) 0 (+) 0` and
   `f_1 r f_2 r f_1 = mq (+) 0 (+) 0`. The unital surjection `e_j -> f_j`, `p -> r`
   pulls the amplified quasitrace back to a bounded 2-quasitrace `sigma` on `Q` with
   `sigma(h + k) - sigma(h) - sigma(k) = eps D(y, beta q) != 0`.

The converse is trivial, so the route is an equivalence.
