---
rg: 2
id: rf-fp-separability-reduction-proof
kind: route
title: Finitely many commutation relations present the centralizing HNN extension
target: rf-fp-completeness-reduces-to-subgroup-separability-hardness
requires:
  - centralizing-hnn-is-residually-finite-iff-edge-is-separable
---

`K = F x F` is finitely presented and residually finite.  For a finite
tuple `w`, imposing `[v, w_i] = 1` for the finitely many generators of
`L_w` makes `v` commute with all of `L_w`, so (RS1) presents the
centralizing HNN extension `K *_{L_w} (L_w x Z)` on finitely many
generators and relations, computably in `w`.  Now (RS2) is the criterion,
and (RS3) is the composition of a many-one reduction with an upper bound.
