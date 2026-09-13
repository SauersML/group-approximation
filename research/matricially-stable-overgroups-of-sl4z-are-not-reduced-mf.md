---
rg: 2
id: matricially-stable-overgroups-of-sl4z-are-not-reduced-mf
kind: claim
title: A point-norm matricially stable group containing SL_4(Z) has non-MF reduced C-star algebra
distinct_from:
  map-matricial-stability-non-mf: that uses matricial stability and minimal almost periodicity to make a group not MF even as a group; this keeps the group residually finite and uses the Magee--de la Salle fixed vector to make only its reduced algebra non-MF.
---

ESTABLISHED (unreviewed).  Let `Gamma` be a countable group containing
`SL_4(Z)` that is point-norm matricially stable in the sense of Dadarlat
(`dadarlat-matricial-stability-obstruction`, Section 1): every operator-norm
asymptotic homomorphism `phi_n : Gamma -> U(k_n)` admits homomorphisms
`pi_n : Gamma -> U(k_n)` with `||phi_n(g) - pi_n(g)|| -> 0` for each `g`.
Then `C*_r(Gamma)` is not MF.

In particular, if `SL_4(Z)` itself is matricially stable
(`sl4z-matricially-stable`), then `C*_r(SL_4(Z))` is not MF, and the Kazhdan
vertex route through `SL_d(Z)`, `d >= 4`, is closed in the approximate sense
as well.  The hypothesis cannot be weakened to *weak* matricial stability
(padding by genuine representations), because the padding may itself carry the
norm-4 eigenvalue.
