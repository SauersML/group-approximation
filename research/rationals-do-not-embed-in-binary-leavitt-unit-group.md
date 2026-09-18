---
rg: 2
id: rationals-do-not-embed-in-binary-leavitt-unit-group
kind: claim
title: The additive group of the rationals does not embed in the unit group of the binary Leavitt algebra over F_2
invalidates:
  - gl-n-q-bh-via-binary-leavitt-unit-group
distinct_from:
  rationals-embed-in-binary-leavitt-unit-group: that is the positive statement, the negation of this claim.
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

**Necessary conditions for a copy (lane gq-ring-alt, 2026-09-18).**
- Its span is a commutative subalgebra inside `[R,R]` (`leavitt-germ-traces-satisfy-frobenius`, part 4).
- Every nonzero element has infinite centralizer rank (`unit-roots-divide-centralizer-rank`).

**Calibration: this claim is at least as hard as Ara--Cortiñas Question 5.7 over `F_2`.**
- By `diagonal-copy-nonconjugacy-from-no-rationals` it implies `leavitt-units-are-not-conjugate-to-diagonal-copies`.
- That implies `no-unital-map-from-leavitt-tensor-square-to-leavitt-over-f2`
  (`tensor-square-nonembedding-from-no-diagonal-conjugacy`).
- The mechanism is `tbar-embeds-in-laurent-leavitt-unit-group`: any infinite-order unit in a relative commutant
  embeds `L ⊗ F_2[t^±1]`, hence `T̄` and `(Q,+)`, in `U`.
- A proof must therefore exclude infinite-order units from every relative commutant.

**Mod-2 reduction of the integral copy: dead.** The divisible element of `integral-leavitt-unit-group-contains-q`
is a transvection, and it has order 2 over `F_2`. The elements this lane found conjugate to their diagonal copies
are constant matrices over `F_2`, and these are torsion in characteristic 2
(`infinite-order-leavitt-unit-conjugate-to-its-diagonal-copy`, Attempts).
