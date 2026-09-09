---
rg: 2
id: jacobson-168-point-coset-twist-countermodel-proof
kind: route
title: Twist one regular GL3 packet on a single dihedral coset and exhibit the moved label
target: jacobson-positive-root-gluing-misses-laurent-coherence
requires: []
artifacts:
  - research/artifacts/jacobson-missing-laurent-coherence-word-and-finite-cell-countermodel-2026-09-08.md
---

Section 3 of the artifact gives the complete finite construction.
In `B=GL_3(F_2)`, put `h=w_12`, `r=x_23`, `q=w_23`,
`u=x_21`, `v=x_12`, and `d=x_13`. The group `<h,r>` is
dihedral of order eight and `<h,u,r>` is `S_4`.

On the set `B`, let `T(x)=x h` for `x in <h,r>` and let
`T` fix every other label. It centralizes left multiplication by
`h,r,d`, so conjugating the second full regular packet by `T`
preserves its common positive root `c=d` and the entire selected
`S_4` cell. The other packet and the Weyl braid are unchanged.

The coherence word is `L_q T L_v T L_q L_d`. It sends `q`
to `q h`, because `q d q=v` lies outside the dihedral subgroup
and `T(1)=h`. The two opposite-root permutations differ already
at `1`: they send it to `k h` and `k`, respectively. This
verifies both the satisfied equations and the precise omitted one.
