---
rg: 2
id: fpbs-universal-intrinsic-l2-rate-route
kind: route
title: Right-continuity of the intrinsic ball growth rate carries a positive rate at p_u down to p_u, while sharpness and BK pin the rate to zero on [0,p_c]
target: fpbs-benjamini-schramm-universal
requires:
  - fpbs-intrinsic-l2-rate-closed-zero-set
  - fpbs-intrinsic-growth-rate-positive-at-pu
---

Complete route. Let `G` be a nonamenable Cayley graph.

**Not a duplicate of the other routes into the goal.**

- `fpbs-universal-connectivity-operator-route` needs boundedness of
  `T_(p_c)`, which is open universally. Here the critical side is ESTABLISHED
  on every nonamenable Cayley graph, and all the open content is on the
  uniqueness side of `p_u`.
- `fpbs-bs-via-sphere-two-point-rate` uses extrinsic sphere rates. Here the
  kernels are truncated by chemical distance, which is what gives
  submultiplicativity through BK.
- `fpbs-universal-pivotal-rate-contradiction-route` uses pivotals. Here there
  are no pivotals and no integration in the parameter.

1. If `p_u = 1`, then `p_c <= 1/gr < 1 = p_u`. See the calibration in
   `fpbs-intrinsic-l2-rate-bounded-below-above-pu`.
2. Otherwise `p_u < 1`, and `lambda_1(p_u) > 0` by
   `fpbs-intrinsic-growth-rate-positive-at-pu`.
3. By `fpbs-intrinsic-l2-rate-closed-zero-set`, item 3, `lambda_1 = 0` on
   `[0,p_c]`. So `p_u` is not in `[0,p_c]`, which means `p_c < p_u`.

**Decomposition recorded.** The flagship statement is split as follows.

- **(Z)** The rates `lambda_1` and `Lambda` vanish on `[0,p_c]` and are
  right-continuous. This is ESTABLISHED universally, using only BK in the
  intrinsic radius and sharpness. Unlike the critical `l2` conjecture, it needs
  no bound on `||T_(p_c)||`.
- **The open side** is a chain of sufficient conditions, each strictly
  stronger than the next and each stated only for `t > p_u`:
  - (UCS) `fpbs-uniform-chemical-stretch-above-pu`;
  - (IL2) `fpbs-intrinsic-l2-rate-bounded-below-above-pu`;
  - (IL1) `fpbs-intrinsic-growth-rate-positive-at-pu`.

  The implications are recorded in `fpbs-intrinsic-l2-rate-via-uniform-stretch`
  and `fpbs-intrinsic-growth-rate-via-l2-rate`. (UCS) and (IL2) can each fail
  on a graph that has a window, so they are prerequisites that can fail on their
  own. (IL1) is close to a restatement.

**Relation to the wave-4 obstructions.** Soft collapse families, including
`fpbs-sharp-dominating-collapse-over-sparse-spines`, have no BK inequality. So
(Z) is exactly the product-structure step those obstructions demand, and it is
not refuted by them. On the open side, item 6 of the established claim shows
that the linear stretch constant diverges as `t ↓ p_c` on every graph. A proof
of (UCS) must therefore use some property that separates `p_u` from `p_c` in
the uniqueness phase. This is where the attempt in
`fpbs-uniform-chemical-stretch-above-pu` stops.
