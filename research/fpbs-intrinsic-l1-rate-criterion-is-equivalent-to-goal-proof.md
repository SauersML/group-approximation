---
rg: 2
id: fpbs-intrinsic-l1-rate-criterion-is-equivalent-to-goal-proof
kind: route
title: The zero set of lambda_1 is exactly [0,p_c], so positivity at p_u is p_u > p_c
target: fpbs-intrinsic-l1-rate-criterion-is-equivalent-to-goal
requires:
  - fpbs-intrinsic-growth-rate-positive-above-pc
  - fpbs-intrinsic-rates-log-lipschitz-in-parameter
  - fpbs-intrinsic-l2-rate-closed-zero-set
---

Complete written proof. No computation is used.

**Item 1.** Assume `p_u < 1`.

- (`p_c < p_u` => (IL1)). Then `p_u in (p_c,1]`. Item 1 of
  `fpbs-intrinsic-growth-rate-positive-above-pc` gives `lambda_1(p_u) > 0`,
  and `E_(p_u)|B^int_R(o)| >= e^(lambda_1(p_u) R)` for every `R >= 1`. This
  is (IL1) with `delta = lambda_1(p_u)`.
- ((IL1) => `p_c < p_u`). Item 3 of
  `fpbs-intrinsic-rates-log-lipschitz-in-parameter` gives `lambda_1 = 0` on
  `[0,p_c]`. If `p_u <= p_c` then `lambda_1(p_u) = 0`, contradicting (IL1).
  (Since `p_c <= p_u` always, this means `p_u = p_c` is excluded.)

The equivalent forms of (IL1) listed in the claim
`fpbs-intrinsic-growth-rate-positive-at-pu` come from items 1, 2 and 5 of
`fpbs-intrinsic-l2-rate-closed-zero-set`; the argument above uses only
`lambda_1(p_u) > 0`, and the uniform-in-`R` form follows from
`lambda_1 = inf_R R^(-1) log E|B^int_R|` (item 1 there).

**Item 2.** `Gamma` is nonamenable, so it has exponential growth and
`gr(G) = lim_n |B_n(o)|^(1/n) > 1`. For `t > 1/gr`, the expected cluster size
satisfies `chi(t) >= sum_v t^(d(o,v))`, because a geodesic from `o` to `v` is
open with probability `t^(d(o,v))`; the sum is `sum_n |S_n| t^n = infinity`.
Bernoulli bond percolation on a transitive graph has `p_c = p_T` (the
sharpness theorem of Menshikov and of Aizenman--Barsky), so `p_c <= 1/gr < 1 =
p_u`. This is the same argument as Step 1 of
`fpbs-universal-intrinsic-l2-rate-route` and its calibration in
`fpbs-intrinsic-l2-rate-bounded-below-above-pu`.

**Item 3.** Items 1 and 2 give, for each `G`, that `p_c(G) < p_u(G)` iff
either `p_u(G) = 1` or (IL1) holds for `G`. Quantifying over `G` gives the
equivalence with the goal. The route `fpbs-universal-intrinsic-l2-rate-route`
proves the goal from (IL1) plus its Step 1 (the case `p_u = 1`, which is item
2), so its only open prerequisite is equivalent to its target.

**Item 4.** By item 1 of `fpbs-intrinsic-growth-rate-positive-above-pc`,
`lambda_1(q) > 0` for `q in (p_c,1]`, and by item 3 of
`fpbs-intrinsic-rates-log-lipschitz-in-parameter`, `lambda_1(q) = 0` for
`q in [0,p_c]`. So `lambda_1(q) > 0` iff `q > p_c`. The uniform form
`E_q|B^int_R| >= e^(delta R)` for all `R` is equivalent to `lambda_1(q) > 0`
by the inf formula. And `p_lambda1 = p_c` (item 2 of the first node), so
`p_lambda1 < q` iff `p_c < q`. QED.
