---
rg: 2
id: rationals-do-not-embed-in-binary-leavitt-unit-group
kind: claim
title: The additive group of the rationals does not embed in the unit group of the binary Leavitt algebra over F_2
invalidates:
  - gl-n-q-bh-via-binary-leavitt-unit-group
distinct_from:
  leavitt-unit-group-has-no-integer-heisenberg-subgroup: that excludes H_3(Z); this excludes (Q,+), which has no Heisenberg subgroup and no distorted element, so neither exclusion implies the other.
  thompson-units-have-few-roots-in-leavitt-unit-group: that proves no nonzero element of a copy of (Q,+) is a conjugate of an infinite-order Thompson unit; this asks that no copy exists at all.
  gl-n-q-embeds-in-binary-leavitt-unit-group: that is the positive embedding question for GL_n(Q), n >= 2; this is its obstruction, since (Q,+) <= GL_n(Q).
---

**OPEN.** Let `U = L_(F_2)(1,2)^x`. There is no injective homomorphism `(Q,+) -> U`.

**Consequences.**
- `(Q,+) <= GL_n(Q)` for `n >= 2`, as the matrices `[[1,q],[0,1]]`. So this claim kills
  `gl-n-q-embeds-in-binary-leavitt-unit-group` and invalidates `gl-n-q-bh-via-binary-leavitt-unit-group`.
- It also excludes `Aff(Q)`, `SL_2(Q)` and `U_3(Q)` from `U`.
- It is the Leavitt-unit analogue of Higman's theorem that `V` contains no `(Q,+)` (survey arXiv:2306.16356v3,
  Theorem 4.4).

**Status of the pieces.**
- Proved: every nonzero element of a copy of `(Q,+)` in `U` has infinite centralizer rank
  (`unit-roots-divide-centralizer-rank`). It is not a conjugate of an infinite-order Thompson unit
  (`thompson-units-have-few-roots-in-leavitt-unit-group`).
- Missing: a rank bound for genuinely linear units. Route
  `no-rationals-in-leavitt-units-from-finite-centralizer-rank` reduces this claim to the open
  `leavitt-unit-centralizers-have-finite-rank`.

## Attempts

None beyond the reduction above.
