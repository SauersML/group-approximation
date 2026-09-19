---
rg: 2
id: atlas-a4-outer-extremizer-normal-profile-proof
kind: route
title: Enumerate the collision conjugacy class and its products through length four
target: atlas-a4-outer-extremizer-normal-profile
requires:
  - atlas-a4-classical-two-holonomy-profile
---

The exact verifier selects the ten outer alignments with defect numerators
`(84,16)`.  For each it computes the order and fixed-space defect of `q`,
`gamma_c`, and `gamma_a`, enumerates the conjugacy class of `q` under all
`20160` elements of `GL_4(F_2)`, and obtains class size `105`.

To determine normal length, it first tests membership in that class, then all
products of two class elements, then a two-letter product times one class
element, and finally membership among products of two stored two-letter
products.  It returns length four for `gamma_c` and length two for
`gamma_a` in all ten cases.  A separate breadth-first Cayley enumeration on
`q,gamma_c,gamma_a` reaches exactly `20160` matrices.  Assertions pin the
number of extremizers, and the JSON artifact records every matrix, order,
defect numerator, product invariant, and normal length.
