---
rg: 2
id: minimal-subshift-crossed-product-is-not-finitely-presented
kind: claim
title: The crossed product algebra of an infinite minimal subshift over a finite field is not finitely presented
distinct_from:
  minimal-subshift-algebra-is-simple-lef-ring: that proves the ring is finitely generated, simple and LEF; this draws the consequence that it has no finite presentation, as a ring or as an algebra.
  periodic-approximable-subshifts-host-no-fp-simple-group: that excludes finitely presented simple subgroups of the topological full group; this excludes a finite presentation of the coefficient algebra of the elementary group.
---

**ESTABLISHED.** Let `q` be a prime power and `X` an infinite minimal subshift. Then
`R = LC(X, F_q) ⋊ Z` is not finitely presented as a unital ring, and not as an `F_q`-algebra.

**Why it matters.** `EL_3(R)/Z` is the reviewed infinite simple Kazhdan LEF group answering
Pestov 9.1. It is not finitely presented, since finitely presented LEF groups are residually
finite. This claim says that the defect sits already in the ring. Any finitely presented variant
of that construction has to change the coefficient ring, not only the rank of the elementary
group.

Route: `minimal-subshift-crossed-product-is-not-finitely-presented-proof`.
