---
rg: 2
id: fp2-iff-quotient-of-fp-group-by-perfect-normal-subgroup
kind: claim
title: "A group is of type FP_2 exactly when it is a finitely presented group modulo a perfect normal subgroup"
---

A group `G` is of type FP_2 (over `Z`) if and only if `G ≅ H/N` for some
finitely presented group `H` and some perfect normal subgroup `N` of `H`.

Two consequences used downstream:

1. If `Q` is of type FP_2 and `M` is a perfect normal subgroup of `Q`, then
   `Q/M` is of type FP_2.
2. The normal closure of any family of perfect subgroups is perfect.

So killing perfect subgroups preserves type FP_2. This is the mechanism
behind Leary's Theorem 19.2 (arXiv:1512.06609v4: when `π_1(L)` is perfect,
`G_L(S)` is of type FP_2(Z)), and the characterization is standard (Bieri's
Queen Mary notes). Proof in `fp2-iff-quotient-of-fp-group-by-perfect-normal-subgroup-proof`.
