---
rg: 2
id: full-cantor-prefix-compression-and-partition-proof
kind: route
title: Localize group elements by prefix identifications and split partition stabilizers into their supported factors
target: full-binary-cantor-groups-have-copy-stabilizers
requires: []
artifacts:
  - research/artifacts/boone-higman-full-cantor-clopen-action-2026-09-08.md
---

For nonempty clopen U, choose a finite prefix bijection f:C->U.
For example, write U as a disjoint union of k cones, partition
C into k binary cones, and match them by prefix replacements.
Such f need not be a global element of V, since it is not onto C.
However every sufficiently small restriction of f or f^-1 extends
to an element of V: both its domain and range can be chosen
proper cones, and the two complements can be refined to equal
binary leaf counts.

For g in D, define lambda_U(g) to act as f*g*f^-1 on U and
as the identity outside U. Near a point of U this agrees with
v_2*g*v_1 for suitable v_1,v_2 in V extending the necessary local
prefix maps. Continuity lets us shrink the neighborhood so that
both agreements apply. Outside U it agrees with the identity.
Fullness of D therefore puts lambda_U(g) in D(U).

Conversely, for k in D(U), the homeomorphism f^-1*k*f of C
locally agrees with elements of D by the same prefix-extension
argument. Fullness puts it in D, and lambda_U sends it to k.
Thus lambda_U is an isomorphism D->D(U). For U=C take f=id.

Now suppose g preserves every part U_i of a finite clopen
partition. Its restriction to U_i, extended by the identity
off U_i, locally agrees with g or the identity, so belongs
to D by fullness. These supported restrictions commute and
multiply to g. Their intersections are trivial, and conversely
any tuple of supported elements gives a partition stabilizer.
This proves the direct-product decomposition.

A tuple of clopen sets determines a finite partition by its
nonempty Boolean atoms. Its pointwise stabilizer in the action
on clopen sets preserves every atom, hence is a direct power
of D. The subgroup preserving the family setwise permutes the
finitely many members, with that pointwise stabilizer as a
finite-index kernel. The asserted finiteness properties follow
from finite products and finite extensions.

This proof uses fullness in both directions of the localization
isomorphism. It does not infer fullness just from containing V.
