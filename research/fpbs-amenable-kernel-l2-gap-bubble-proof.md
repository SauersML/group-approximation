---
rg: 2
id: fpbs-amenable-kernel-l2-gap-bubble-proof
kind: route
title: Evaluate the fibre operator on the identity coset and use equality of norms for amenable kernels
target: fpbs-amenable-kernel-l2-gap-forces-fibre-bubble
requires:
  - fpbs-fibre-summed-connectivity-operator
artifacts:
  - research/artifacts/fpbs/docs/rd-weighted-fibre-bubble-criterion.md
---

1. `p_{2->2}` is the supremum of `p` with `||T_p|| < infinity`, and `||T_p||` is
   nondecreasing in `p`. So `p_c < p_{2->2}` gives `||T_(p_c)|| < infinity`.
2. For amenable `H`, `fpbs-fibre-summed-connectivity-operator` gives
   `||S_(p_c)|| = ||T_(p_c)||`.
3. The critical fibre bubble is `||S_(p_c) delta_1||_2^2`, which is at most
   `||S_(p_c)||^2`.

Artifact Section 2.
