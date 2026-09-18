---
rg: 2
id: fpbs-intrinsic-growth-rate-positive-above-pc
kind: claim
title: On every nonamenable Cayley graph the intrinsic ball growth rate is positive at every supercritical parameter, so its zero set is exactly [0,p_c]
distinct_from:
  fpbs-intrinsic-growth-rate-positive-at-pu: that is (IL1), positivity of lambda_1 at the single parameter p_u; this is positivity on the whole supercritical interval (p_c,1], which makes (IL1) equivalent to p_c < p_u (recorded in fpbs-intrinsic-l1-rate-criterion-is-equivalent-to-goal)
  fpbs-intrinsic-l2-rate-closed-zero-set: that proves lambda_1 = 0 on [0,p_c] and p_c <= p_lambda1; this proves the reverse inequality p_lambda1 <= p_c from anchored expansion
  fpbs-intrinsic-rates-log-lipschitz-in-parameter: that gives the upper bound lambda_1(t) <= log(t/p_c) and continuity; this gives the matching positivity lambda_1(t) > 0 for t > p_c
  fpbs-hermon-hutchcroft-anchored-expansion: that is the published almost-sure isoperimetric statement for infinite clusters; this is its consequence for the expected intrinsic ball volume, the quantity the intrinsic-rate route is built on
---

**ESTABLISHED.** Proof in `fpbs-intrinsic-growth-rate-positive-above-pc-proof`.

**Setting.** As in `fpbs-intrinsic-l2-rate-closed-zero-set`:
`G = Cay(Gamma,S)` with `Gamma` finitely generated and nonamenable,
`D = |S|`, `B^int_R(o)` the intrinsic (chemical) ball of radius `R` about the
identity `o` in its open cluster, and

```text
lambda_1(t) = lim_R (1/R) log E_t |B^int_R(o)| = inf_R (1/R) log E_t |B^int_R(o)|,
p_lambda1   = sup { t : lambda_1(t) = 0 }.
```

**Theorem.**

1. For every `t in (p_c,1]`, `lambda_1(t) > 0`. Quantitatively, if
   `phi > 0` satisfies `P_t(|K_o| = infinity, Phi*_E(K_o) > 2 phi) > 0`, then
   `lambda_1(t) >= log(1 + phi/D)`. Hence `E_t|B^int_R(o)| >= e^(lambda_1(t) R)`
   for **every** `R >= 1`.
2. `p_lambda1 = p_c`. Together with the ESTABLISHED
   `fpbs-intrinsic-rates-log-lipschitz-in-parameter`, `lambda_1` is continuous,
   vanishes exactly on `[0,p_c]`, and satisfies `0 < lambda_1(t) <= log(t/p_c)`
   on `(p_c,1]`.

**What this settles.** The OPEN claim `fpbs-intrinsic-growth-rate-positive-at-pu`
(IL1) asks for `lambda_1(p_u) > 0`. By item 2 that holds exactly when
`p_u > p_c`. So (IL1) is the goal restated, and the route
`fpbs-universal-intrinsic-l2-rate-route` carries no content beyond the goal.
The equivalence is recorded in
`fpbs-intrinsic-l1-rate-criterion-is-equivalent-to-goal`.

**Where transitivity is used.** Only in the imported anchored expansion
(`fpbs-hermon-hutchcroft-anchored-expansion`). Hermon and Hutchcroft
(arXiv:1904.10448v3, Remark 3.6) note that `Z^3` with a binary tree attached at
each vertex is nonamenable, has `p_c = p_c(Z^3) < 1/2`, and for
`p_c < p < 1/2` has a unique infinite cluster of subexponential growth. So on
bounded-degree nonamenable graphs that are not transitive, the intrinsic l1
rate can vanish above `p_c` (recalled as calibration; not used).
