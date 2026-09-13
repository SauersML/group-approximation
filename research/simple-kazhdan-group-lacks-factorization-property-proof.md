---
rg: 2
id: simple-kazhdan-group-lacks-factorization-property-proof
kind: route
title: Proof — infinite simple plus (T) is not residually finite, so Kirchberg denies the factorization property
target: simple-kazhdan-group-lacks-factorization-property
requires:
  - continuum-many-simple-kazhdan-lef-groups
  - kirchberg-property-t-fp-implies-rf
---
`continuum-many-simple-kazhdan-lef-groups` gives that `G_X` is infinite, finitely
generated, simple, has property (T), and is LEF (hence sofic and hyperlinear).

Not residually finite: a finite quotient of a simple group is either trivial or
injective; an injective finite quotient forces `G_X` finite, which it is not, so the
only finite quotient of `G_X` is trivial and the intersection of finite-index
subgroups is all of `G_X`. So `G_X` is not residually finite.

`kirchberg-property-t-fp-implies-rf`: a property (T) group has the factorization
property iff it is residually finite. `G_X` has property (T) and is not residually
finite, so it does not have the factorization property. LEF gives sofic and
hyperlinear. This is the claim.
