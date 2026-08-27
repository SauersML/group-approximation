---
rg: 2
id: kac-moody-dichotomy-proof
kind: route
title: Instantiate the non-RF Kazhdan equivalence at the Caprace-Remy groups
target: kac-moody-lattice-is-non-hyperlinear-or-llp-failure
requires:
  - simple-kazhdan-kac-moody-lattices-exist
  - llp-non-rf-kazhdan-group-is-non-hyperlinear
  - non-rf-kazhdan-weak-ucp-iff-non-hyperlinear
---

`Lambda` is finitely generated (finitely presented), Kazhdan, and infinite
simple, hence not residually finite
(`simple-kazhdan-kac-moody-lattices-exist`).  If `Lambda` is hyperlinear,
then by `non-rf-kazhdan-weak-ucp-iff-non-hyperlinear` it is neither weakly
ucp-stable nor flexibly HS-stable on hyperlinear approximations, and by
`llp-non-rf-kazhdan-group-is-non-hyperlinear` (contrapositive)
`C^*(Lambda)` fails LLP.  If `Lambda` is not hyperlinear, it is the goal's
witness, finitely presented and simple.  The two cases are exclusive by
definition.
