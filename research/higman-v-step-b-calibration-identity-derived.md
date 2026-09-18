---
rg: 2
id: higman-v-step-b-calibration-identity-derived
kind: claim
title: The infinite-order Step-B core instance (0,10)(0,1000) is settled in the all-swaps quotient of V_2 by seven relator steps, with a Lean certificate
artifacts:
  - GroupApproximation/BooneHigman/Join/HigmanVCalibCore.lean
  - GroupApproximation/BooneHigman/Join/HigmanVCalibration.lean
---

**ESTABLISHED (lane `bh-pal-met-join`).** Lean status: BUILD_STATUS_PLACEHOLDER

This follows up and corrects `higman-v-step-b-core-local-conjugation-and-f-obstruction`
(cbcd58208). That node's item C.5 left the identity below as an open calibration target and
suggested an MSI search. No search was needed: it has a short hand derivation, which is now
formalized. The node's Claims A and B and items C.1–C.4 stand as written.

## Statement

In `Q = higmanVCCommon_Q 2` (all-swaps free group modulo `higmanVC_rels 2`), with
`ℓ(x,y) = mk (of (x, y))`:

`ℓ(0,10) · ℓ(0,1000) = ℓ(00,10) · ℓ(00,1000) · ℓ(01,101) · ℓ(01,1001)`.

- The left side is the hard Step-B core instance of cbcd58208, Claim C: `h = ℓ(0,10)`,
  `P = ℓ(0,1000)`. Its image in `V_2` has infinite order.
- The right side is `ℓ(00,10)` times an element of the antichain subgroup on
  `{00, 01, 1000, 1001, 101, 11}`, so this instance lies in `S = U · ⋃ H_A · U`.

Lean:
- `GroupApproximation.BooneHigman.Join.calib_of_relators` proves the identity in ANY group with a
  map `ℓ` satisfying the involution, conjugation and split relators. It is Mathlib-only, plus
  `BooneHigman.V.ConeSwap`.
- `qLetter_calibration` instantiates it in `Q`.

## Derivation (seven relator steps)

1. `ℓ(0,10) ℓ(0,1000) ℓ(0,10)⁻¹ = ℓ(10,000)`: conjugation, since `(0 10)` maps `0 ↦ 10`
   and `1000 ↦ 000`.
2. `ℓ(00,10) ℓ(10,000) ℓ(00,10)⁻¹ = ℓ(00,100)`: conjugation, with `10 ↦ 00` and
   `000 ↦ 100`.
3. Split relators: `ℓ(0,10) = ℓ(00,100) ℓ(01,101)` and `ℓ(00,10) = ℓ(000,100) ℓ(001,101)`.
4. `ℓ(00,100)` conjugates `ℓ(000,100)` to `ℓ(1000,00)` and `ℓ(001,101)` to `ℓ(1001,101)`.
   The word `101` is fixed, since it is incomparable with `00` and with `100`.
5. `ℓ(01,101)` conjugates `ℓ(1001,101)` to `ℓ(1001,01)`.
6. Use symmetry `ℓ(x,y) = ℓ(y,x)` (conjugation by the letter itself) and the involutions.

The group identity that assembles these steps is `calib_alg`.

**Lesson for general BH.** The Thompson-`F` obstruction of cbcd58208 is an obstruction to
*static* symmetrization (Claim B data), not to short derivations. Conjugating the deep letter
by the shallow swap first moves the defect onto one antichain in a bounded number of steps.

Open question: does "conjugation-first rewriting" terminate for every Step-B core instance?
If it does, with a measure that decreases at each step, then H1 (`HigmanVCStepBCoreStatement`)
closes by induction. This was not examined beyond this instance. A bounded MSI search on
random core instances, with a planted positive, is the cheap test.
