---
rg: 2
id: simple-kazhdan-group-lacks-factorization-property
kind: claim
title: The simple Kazhdan LEF subshift group has no factorization property, so it is a simple sofic group strictly beyond residual amenability
distinct_from:
  binary-leavitt-unit-group-fails-factorization-property: that node is the paradoxical Leavitt unit group L(1,2)^× (nonsofic, no MF quotient); this node is the measure-side subshift group G_X, which is LEF, sofic and hyperlinear.
---
Let `X` be an infinite minimal subshift and `G_X = EL_3(LC(X,F_2) ⋊_T Z)`, the
infinite finitely generated simple Kazhdan LEF group of the note (see
`continuum-many-simple-kazhdan-lef-groups`). Then `G_X` does not have Kirchberg's
factorization property.

An infinite finitely generated simple group has no nontrivial finite quotient, so
`G_X` is not residually finite. It has property (T). By
`kirchberg-property-t-fp-implies-rf`, a property (T) group has the factorization
property iff it is residually finite, so `G_X` lacks it. Since `G_X` is LEF it is
sofic and hyperlinear. So `G_X` is an infinite simple group that is hyperlinear but
without the factorization property, placing it strictly on the hyperlinear side of
Kirchberg's dichotomy.

Prior art: Thom (2010, Groups Geom. Dyn. 4) already produced finitely generated
Kazhdan LEF non-residually-finite groups, hence hyperlinear without the factorization
property; the new element here is simplicity. This is a placement of `G_X` in the
Kirchberg--Ozawa landscape, not a new theorem.
