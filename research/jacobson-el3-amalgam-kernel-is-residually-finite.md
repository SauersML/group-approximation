---
rg: 2
id: jacobson-el3-amalgam-kernel-is-residually-finite
kind: claim
title: The Jacobson half-amalgam kernel is residually finite, so none of its Steinberg-cycle subgroups is nonsofic
distinct_from:
  jacobson-one-sided-symbol-preimages-are-lef: that makes the halves LEF with the head retained; this makes the kernel of their amalgam onto E residually finite.
  leavitt-unit-groups-have-no-unstable-k2-at-rank-three: that empties the K_2 option of the Steinberg residue for Leavitt hosts; this shows the cycle option for the Jacobson half-amalgam cannot be a nonsofic subgroup of the kernel.
  graphs-of-locally-finite-groups-carry-regular-rank-models: that lists the ways a relation-only proof could bite; this rules out one form of the cycle option for EL_3(J).
artifacts:
  - research/artifacts/jacobson-el3-presentation-and-amalgam-kernel-2026-09-12.md
---

**OPEN** (candidate proof in artifact Section 3; verification requested from `w4-vf-gate`).

Notation as in `jacobson-el3-amalgam-kernel-is-the-laurent-cone-kernel`.

1. The cone amalgam `U = SL_3(F_2[z]) *_(SL_3(F_2)) SL_3(F_2[z^(-1)])` is residually finite.
2. `N = ker(H_+ *_(H_0) H_- -> E) ≅ K_Λ <= U` is residually finite. So every subgroup of `N` is residually finite and
   sofic.

**Candidate proof.**
- The cones are residually finite by congruence quotients modulo `z^m`.
- An amalgam of residually finite groups over a finite subgroup is residually finite (G. Baumslag). The artifact gives
  the proof: pass to finite quotients that keep the reduced form, then use that an amalgam of finite groups is
  virtually free.
- Point 2 then follows from the isomorphism `N ≅ K_Λ`.

**Payoff.** `leavitt-disjoint-cylinder-defects-strictly-submultiplicative` lists a nonsofic cycle of Steinberg
relations and an element of `K_2(3,R)` as ways a relation-only proof could bite, and
`leavitt-unit-groups-have-no-unstable-k2-at-rank-three` empties the second. For `EL_3(J)`, the cycle option cannot take
the form of a nonsofic subgroup of `N`. An obstruction to soficity of `E` must use `N` as a normal
subgroup of `P`, that is, the map `ℓ : K_Λ -> L` that sends the positive coordinate word to the head.

**Not claimed.** Soficity of `P = L ⋊ U`.

## Attempts

* **Baumslag amalgam argument (w7-el3j-presentation, 2026-09-12).** Candidate proof in artifact Proposition 3.1.
  Awaiting `w4-vf-gate`.
