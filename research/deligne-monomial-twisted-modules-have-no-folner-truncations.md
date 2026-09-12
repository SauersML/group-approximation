---
rg: 2
id: deligne-monomial-twisted-modules-have-no-folner-truncations
kind: claim
title: No monomial module of Deligne's triple cover with nontrivial central character has Folner coordinate truncations
distinct_from:
  deligne-fixed-projective-representation-folner-compression-no-go: that excludes HS Folner compressions of an exact unitary projective representation, through amenable traces; this excludes coordinate Folner truncations of monomial modules over fields of characteristic p != 3, through almost invariant vectors on the coordinate set and finite abelianization.
  deligne-twisted-fibres-have-no-amenable-trace: that is the C-star trace obstruction on the twisted fibres; this is a combinatorial statement about Gamma-sets carrying a twisted monomial module, and needs no trace.
artifacts:
  - research/artifacts/deligne-twisted-group-algebras-2026-09-12.md
---

Let `E_3` be Deligne's triple cover of `Gamma = Sp_4(Z)`, `F` a field of characteristic `p != 3` containing a
primitive cube root of unity `w`, and `M` an `F[E_3]`-module on which `z` acts as `w^j` with `j in {1, 2}`.
Suppose `M` has a basis `X` whose vectors every element of `E_3` sends to nonzero multiples of basis vectors, so
that `Gamma` acts on `X`. Then `X` admits no Folner sequence for `Gamma`.

In particular, truncating one fixed monomial twisted module, such as a twisted induced module over any
subgroup, never gives rank-approximate projective representations of the Deligne multiplier.

**ESTABLISHED 2026-09-12** by `deligne-monomial-twisted-modules-no-folner-proof` (artifact Proposition 3.1).
Verification requested from w4-vf-linear-b.
