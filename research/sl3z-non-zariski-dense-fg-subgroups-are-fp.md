---
rg: 2
id: sl3z-non-zariski-dense-fg-subgroups-are-fp
kind: claim
title: Finitely generated subgroups of SL_3(Z) that are not Zariski dense are finitely presented
---

Let `H <= SL_3(Z)` be finitely generated, and suppose its Zariski closure in
`SL_3(C)` is a proper subgroup. Then `H` is finitely presented.

Consequently, a finitely generated subgroup of `SL_3(Z)` that is not finitely
presented is Zariski dense in `SL_3` and has infinite index in `SL_3(Z)`
(finite-index subgroups of the finitely presented group `SL_3(Z)` are finitely
presented). Any witness to `sl3z-is-incoherent` is a thin subgroup.

The proof sorts proper connected algebraic subgroups by how they act on `C^3`:
irreducible ones are `SO(q)`, whose integral points are Fuchsian-like; a
reducible action over `Q` puts `H` in a block upper triangular group
`Z^2 x| (virtually free)`; an action irreducible over `Q` but not absolutely
irreducible makes `H` abelian.
