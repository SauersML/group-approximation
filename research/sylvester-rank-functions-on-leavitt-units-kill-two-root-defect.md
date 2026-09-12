---
rg: 2
id: sylvester-rank-functions-on-leavitt-units-kill-two-root-defect
kind: claim
title: Every Sylvester rank function on the binary Leavitt unit group algebra kills the two-root defect
refuted_by:
  - binary-leavitt-units-carry-nonaugmentation-rank-function
distinct_from:
  rank-models-of-el3-satisfy-the-two-root-identities: that asks the two-root identity for homomorphisms into rank ultraproducts, whose payoff is non-linear-soficity; this asks it for every Sylvester matrix rank function on the group algebra, which implies that identity for the binary instance and is equivalent to uniqueness of the augmentation rank.
  leavitt-el3-rank-models-over-finite-fields-are-trivial: that is triviality of rank-ultraproduct models over every finite field; this is the binary group-algebra statement over F_2 for every Sylvester rank function, matricial or not.
artifacts:
  - research/artifacts/sylvester-rank-function-two-root-gate-2026-09-12.md
---

**OPEN.** Let `R = L_(F_2)(1,2)`, identify `Γ = R^x` with `EL_3(R)` through the three-leaf prefix code,
and put `D = ([x_23(1)] - 1)([x_12(1)] - 1)` in `F_2[Γ]`. Every Sylvester matrix rank function on
`F_2[Γ]` has `rk(D) = 0`.

**Equivalent forms** (`leavitt-rank-functions-killing-two-root-defect-are-augmentation`).
- The augmentation rank is the only Sylvester matrix rank function on `F_2[R^x]`.
- `binary-leavitt-units-carry-nonaugmentation-rank-function` fails.

**What it gives and what gives it.**
- It makes every characteristic-two rank model of `R^x` trivial, so `R^x` is not `F_2`-linear sofic
  (route `non-linear-sofic-via-sylvester-two-root-gate`).
- Either binary averaging target implies it: `binary-cyclic-averaging-idempotent-is-full-on-leavitt-units`
  or `thompson-v-order-three-averaging-idempotent-is-full` (Corollary 1.3 of
  `research/artifacts/binary-cyclic-corner-rank-function-dichotomy-2026-09-12.md`).
- The ultraproduct gate `rank-models-of-el3-satisfy-the-two-root-identities` for this `R` is its special
  case for matricial rank functions. The converse would need every Sylvester rank function on
  `F_2[R^x]` to be a limit of matricial ones, which is not known.

## Attempts

- **Transfer of the gate tools (lane `w4-rankfn`).** Some tools transfer verbatim to
  `B = F_2[Γ]/I_rk`, because they use only exact group relations, ring identities and the Sylvester
  axioms with faithfulness:
  - Theorems A and D.2 of the two-root artifact;
  - Propositions 6 and 8 and Corollary 9 of the rank-ring rigidity artifact;
  - `toeplitz-isometry-defects-have-total-rank-at-least-one`.

  Arguments using range idempotents, images, Fitting decompositions, idempotent lifting or rounding do
  not transfer as they stand, because `B` need not be regular (artifact Corollary 5).
- **Refuting it, that is, a rank function with `rk(D) > 0`.** Artifact Section 3 audits the
  non-matricial sources; none produces one.
  - Rank completions of locally matricial algebras only reproduce linear soficity.
  - Følner compressions of permutation modules are Hamming, so they would make `R^x` sofic.
  - Modules through the evaluation die, because `R` has no rank function and `D` lies in the kernel.
  - Diagonal tensor powers of `R`-modules are an open handle: `D` acts by `e_23 (x) e_12 + e_12 (x) e_23`,
    and densities die because `V` has no invariant measure on `X^n`.
