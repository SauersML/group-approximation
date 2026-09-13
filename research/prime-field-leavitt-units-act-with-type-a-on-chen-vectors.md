---
rg: 2
id: prime-field-leavitt-units-act-with-type-a-on-chen-vectors
kind: claim
title: For every prime p the unit groups of L_(F_p)(1,2) and of L_(F_p)(1,2) ⊗ L_(F_p)(1,2) act with type (A) on the nonzero vectors of their Chen modules
distinct_from:
  leavitt-unit-groups-mod-scalars-satisfy-pbh: that is the quotient by the scalars acting on lines; this is the unit group itself acting on vectors, keeping the central scalars.
  leavitt-square-unit-groups-mod-scalars-satisfy-pbh: that is the tensor-square quotient acting on lines; this is the tensor-square unit group itself acting on vectors.
  binary-leavitt-unit-group-satisfies-pbh: that is the one-factor group over F_2, through the Cantor module extension; this covers every prime and both groups, with no extension.
  two-transitive-action-reduces-type-a-to-two-clauses: that reduces type (A) for 2-transitive actions; the vector action is not 2-transitive once p > 2, because scalar multiples form their own pair orbits, and here those orbits are counted directly.
---

**ESTABLISHED** through `prime-field-leavitt-chen-vector-action-type-a-proof` (not
independently reviewed; no novelty is claimed).

Let `p` be a prime and `L_p = L_(F_p)(1,2)`. Let `U` be `L_p^×` acting on `W = F_p[D]`, or
`(L_p ⊗ L_p)^×` acting on `W = F_p[D × D]`, where `D` is the tail class of `0^∞`. Then the
action of `U` on `W ∖ {0}` is of type (A).

**Consequences.**
- Every subgroup of `U` has solvable word problem and embeds in a finitely presented simple
  group (`type-a-action-gives-boone-higman-for-subgroups`).
- For odd `p` this establishes `prime-field-leavitt-unit-groups-satisfy-pbh` through
  `prime-field-leavitt-pbh-via-chen-module-vectors`.
