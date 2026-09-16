---
rg: 2
id: finite-by-cocompact-fuchsian-groups-are-virtually-surface
kind: claim
title: A finite-by-cocompact-Fuchsian group has a finite-index subgroup isomorphic to a closed hyperbolic surface group
distinct_from:
  one-ended-hyperbolic-groups-contain-surface-subgroups: that asks for a surface subgroup in every one-ended hyperbolic group; this is the elementary case of extensions of cocompact Fuchsian groups by finite groups, where the surface subgroup even has finite index
  kapovich-kleiner-one-dimensional-boundary-classification: that imports which groups are finite-by-Fuchsian (carpet stabilizers, rigid circle groups); this proves that any finite-by-Fuchsian group is virtually a surface group
---

Let `1 -> K -> P -> Phi -> 1` be an extension in which `K` is finite and `Phi` is a
cocompact discrete subgroup of `Isom(H^2)`. Orientation-reversing elements are allowed.

Then `P` has a finite-index subgroup `Sigma` isomorphic to `pi_1(S)` for a closed orientable
surface `S` of genus at least `2`.

In particular, if `P` is a quasiconvex subgroup of a hyperbolic group `G`, then `Sigma` is a
quasiconvex surface subgroup of `G`.

The mechanism: after Selberg's lemma and passing to the centralizer of `K`, one reaches a
central extension of a surface group by the finite abelian group `Z(K)`. Its Euler class in
`H^2(S; Z(K)) = Z(K)` gets multiplied by the degree under finite covers, so it dies on a cover
of degree `|Z(K)|`, where the extension splits.
