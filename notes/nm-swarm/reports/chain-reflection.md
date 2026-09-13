# chain-reflection (S6a): thm:core-ring-reflection

Printed item: `non_mf_groups_exist.tex` lines 1514–1537, `\label{thm:core-ring-reflection}`
and its proof.

WORKLIST keys (census merge 0913-144720):
`42c043ef7ab5` `8981cd70915a` `43afa4ee3f10` `cfbacaa0fffa` `9dae685e37b9` `400dde0dbd9d`
`5a62e295ac1a` `d74779471003` `715cbd0f3410` `30a44485e5e8` `f2baa4a46f78` `b23e0f5197b5`.
Census rows: `metadata/nm-census-rows/chain-reflection.tsv`.

## Carriers reused (origin/main)

- `MFQuotientUnits.Corner`, `cornerRing`, `corner_ext`, `mem_cornerNonUnitalSubring_iff`
  (`Algebra/CornerRing.lean`).
- `MFQuotientUnits.oneSubAddCornerHom` (`Algebra/CornerUnitExtension.lean`): `a ↦ 1 − e + a`,
  the printed "extend a one-sided inverse pair by 1 − e".
- `IsLEFRing`, `isLEFRing_of_finite`, `IsLEFRing.matrix` (`Pestov91/LEF.lean`).
- `Pestov91.IsLEFRing.of_injective` (`Algebra/LEFRingDirectedUnion.lean`, owner chain-itinerary,
  landed 6ac372c36).
- Mathlib (pin 81a5d257): `IsDedekindFiniteMonoid.of_injective`, `IsStablyFiniteRing`,
  `RingHom.liftOfSurjective`, `RingHom.liftOfSurjective_comp`, `RingHom.eq_liftOfSurjective`,
  `RingHom.mapMatrix`, `Matrix.single`, `Matrix.matrix_eq_sum_single`, `Matrix.single_mul_single_same`.

## Modules

1. `GroupApproximation/Algebra/DirectlyFiniteCorner.lean`: LANDED e383572ae, probe 0913-154317-37555
   `# PROBE GREEN`, unwired (queued in wire-queue.txt).  Generic, no upstream.
   - `isDedekindFiniteMonoid_corner`: the corner `eAe` of a directly finite ring is directly finite
     (key `d74779471003`).
   - `matrixUnitCornerHom φ i : R →+* Corner A (φ (single i i 1)) _`, `r ↦ φ (single i i r)`
     (keys `5a62e295ac1a`, `715cbd0f3410`); `coe_matrixUnitCornerHom`, `isIdempotentElem_map_single_one`.
   - `map_eq_zero_of_forall_entry_mem`: if every unital hom `R → B` into a directly finite ring kills
     `I`, then every unital hom `Matrix n n R → A` into a directly finite ring kills `M_n(I)`
     (key `30a44485e5e8`).
2. `GroupApproximation/Algebra/DirectlyFiniteReflection.lean`: LANDED 578ecd818, probe
   0913-160055-80827 `# PROBE GREEN`, unwired (queued).  For a surjective unital `f : R →+* S` with
   `S` LEF and `KillsKernelOfDirectlyFinite f`:
   - `IsUniversalDirectlyFiniteQuotient`, `IsUniversalStablyFiniteQuotient`, `IsUniversalLEFQuotient`
     (universe-explicit, targets in `Type w`), `KillsKernelOfDirectlyFinite`.
   - `existsUnique_comp_eq_of_surjective`, `mapMatrix_surjective_of_surjective`,
     `killsKernelOfDirectlyFinite_mapMatrix`.
   - `isUniversalQuotients_of_surjective` (key `400dde0dbd9d`), `isUniversalQuotients_mapMatrix`
     (keys `43afa4ee3f10`, `f2baa4a46f78`).
   - `directlyFinite_iff_stablyFinite_iff_lef_iff_injective`: abstract half of `cfbacaa0fffa`,
     `b23e0f5197b5`.
   - Model tests: `lefInterfaces_finite_model`, `killsKernelOfDirectlyFinite_of_injective`,
     `reflection_hypotheses_finite_model`, `not_killsKernelOfDirectlyFinite_toZero` (fails for `ℤ → 0`).
   - Per main's duplicate ruling, LEF along injections is chain-itinerary's lemma, imported.
3. `GroupApproximation/Manuscript/NonMFSentences/CoreRingReflection.lean`: printed assembly (later).
   `def PrintedCoreRingReflection : Prop` + `theorem printedCoreRingReflection`, one Prop per sentence
   (keys `42c043ef7ab5`, `8981cd70915a`, `43afa4ee3f10`, `cfbacaa0fffa`, `9dae685e37b9`, `b23e0f5197b5`).
   It instantiates module 2 at restriction `R_X → R_Y`.

## Interfaces consumed (owners' names, from their reports and disks)

- chain-core (S1): `ClopenCrossedProduct T k` (`R_X`), `defectD`, `map_defectD_eq_zero` (landed
  unverified 0c76b1c47 / 32275d037); a restriction map in `ClopenCrossedProductComap` (on disk).
  LEF ⇒ stably finite: still to come.
- chain-matricial (S5), planned: `restrict`, `restrict_surjective`, `ker_restrict_eq_transientIdeal`,
  `transientIdeal_eq_span_defects`, `transientIdeal_eq_bot_iff`.
- chain-itinerary (S4): `IsLEFRing.of_injective` (landed, consumed); planned
  `isLEFRing_crossedProduct_chainRecurrentSet` (`R_Y` LEF).

## Residuals

| Prop / gap | content | discharged by | owner |
|---|---|---|---|
| `LEFStablyFiniteInterface` (Prop in module 2) | `IsLEFRing B → IsStablyFiniteRing B` | S1 LEF ⇒ SF lemma | chain-core S1 |
| defect killed | unital hom `R_X → A`, `A` directly finite, kills each `d` | `map_defectD_eq_zero` | chain-core S1 |
| kernel = `I` = ideal of defects | exactness of `0 → I → R_X → R_Y → 0` | `ker_restrict_eq_transientIdeal`, `transientIdeal_eq_span_defects` | chain-matricial S5 |
| `R_Y` LEF | lem:chain-core-models | `isLEFRing_crossedProduct_chainRecurrentSet` | chain-itinerary S4 |
| `I = 0 ⇔ X = Y` | | `transientIdeal_eq_bot_iff` | chain-matricial S5 |

## Status

- 09-13: plan landed (566d5384e).
- 09-13: DirectlyFiniteCorner landed e383572ae (GREEN 0913-154317-37555), wiring queued.
- 09-13: DirectlyFiniteReflection landed 578ecd818 (GREEN 0913-160055-80827), wiring queued; an
  earlier GREEN (0913-155359-13775) took LEF along injections as a hypothesis Prop and was not landed.
- 09-13: census rows (12 keys: 1 formalized, 1 definition, 10 partial).
- Next: the printed assembly, once chain-core (LEF ⇒ SF, restriction), chain-matricial (kernel = I,
  I = 0 ⇔ X = Y) and chain-itinerary (`R_Y` LEF) land their interfaces.
