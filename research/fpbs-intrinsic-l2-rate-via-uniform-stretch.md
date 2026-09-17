---
rg: 2
id: fpbs-intrinsic-l2-rate-via-uniform-stretch
kind: route
title: Test the intrinsic-radius kernel on balls; a uniform linear stretch constant above p_u gives a uniform positive l2 rate, and right-continuity carries it to p_u
target: fpbs-intrinsic-l2-rate-bounded-below-above-pu
requires:
  - fpbs-intrinsic-l2-rate-closed-zero-set
  - fpbs-uniform-chemical-stretch-above-pu
---

Complete route. Assume `p_u < 1`.

1. By `fpbs-uniform-chemical-stretch-above-pu` there is `K < infinity` that is
   a linear stretch constant at every `t > p_u`.
2. By item 4 of `fpbs-intrinsic-l2-rate-closed-zero-set`,
   `Lambda(t) >= log(gr)/(2K)` for all `t > p_u`. Here `gr > 1` by
   nonamenability.
3. By item 5 there, `Lambda(p_u) >= log(gr)/(2K) > 0`.

Step 2 tests only against indicators of balls. So the averaged hypothesis
`sum_(u,v in B_m) P_t(d_omega(u,v) <= K(2m+1)) >= c_t |B_m|^2` for all `m`
already suffices: the proof of item 4 uses nothing else.
