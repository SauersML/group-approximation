# chain-reflection (S6a): thm:core-ring-reflection

Printed item: `non_mf_groups_exist.tex` lines 1514–1537, `\label{thm:core-ring-reflection}`
and its proof.

WORKLIST keys (census merge 0913-144720):
`42c043ef7ab5` `8981cd70915a` `43afa4ee3f10` `cfbacaa0fffa` `9dae685e37b9` `400dde0dbd9d`
`5a62e295ac1a` `d74779471003` `715cbd0f3410` `30a44485e5e8` `f2baa4a46f78` `b23e0f5197b5`.

## Carriers reused (origin/main)

- `MFQuotientUnits.Corner`, `cornerRing`, `corner_ext` (`Algebra/CornerRing.lean`).
- `MFQuotientUnits.oneSubAddCornerHom` (`Algebra/CornerUnitExtension.lean`): `a ↦ 1 − e + a`,
  the printed "extend a one-sided inverse pair by 1 − e".
- `IsLEFRing`, `IsLEFRing.matrix` (`Pestov91/LEF.lean`).
- Mathlib (pin 81a5d257): `IsDedekindFiniteMonoid`, `IsDedekindFiniteMonoid.of_injective`,
  `IsStablyFiniteRing`, `RingHom.liftOfSurjective`, `RingHom.eq_liftOfRightInverse`,
  `RingHom.mapMatrix`, `Matrix.single`, `Matrix.matrix_eq_sum_single`, `Matrix.single_mul_mul_single`.

Survey (origin/main and every `lanes/*.files`, declarations and uses): no carrier for Dedekind
finiteness of a corner, the universal directly finite / stably finite / LEF quotient, or
`IsLEFRing` transport along an injective ring hom.

## Planned modules (paths free on disk, on origin and in lanes/*.files)

1. `GroupApproximation/Algebra/DirectlyFiniteCorner.lean`: definitions module, generic, no upstream.
   - `isDedekindFiniteMonoid_corner [IsDedekindFiniteMonoid A] (e) (he) :
     IsDedekindFiniteMonoid (Corner A e he)`: key `d74779471003`.
   - `matrixUnitCornerHom (φ : Matrix n n R →+* A) (i0) : R →+* Corner A (φ (single i0 i0 1)) _`,
     `r ↦ φ (single i0 i0 r)`: keys `5a62e295ac1a`, `715cbd0f3410`.
   - `map_eq_zero_of_forall_entry_mem`: if every unital hom `R →+* B` into a directly finite ring
     kills the ideal `I`, then every unital hom `Matrix n n R →+* A` into a directly finite ring
     kills every matrix with entries in `I`: key `30a44485e5e8`.
2. `GroupApproximation/Algebra/DirectlyFiniteReflection.lean`: abstract reflection.
   - `IsUniversalDirectlyFiniteQuotient`, `IsUniversalStablyFiniteQuotient`,
     `IsUniversalLEFQuotient` (`f : R →+* S`, universe-explicit Props).
   - `existsUnique_comp_eq_of_surjective_of_ker_le`.
   - `IsLEFRing.of_injective`.
   - `reflection_of_surjective`: `f` surjective, `S` LEF, every unital hom into a directly finite
     ring kills `ker f` ⇒ all three universal properties for `f` and for `f.mapMatrix` on
     `Fin m`: keys `400dde0dbd9d`, `43afa4ee3f10`, `f2baa4a46f78`.
   - `directlyFinite_iff_stablyFinite_iff_lef_iff_ker_eq_bot`: abstract half of `cfbacaa0fffa`.
3. `GroupApproximation/Manuscript/NonMFSentences/CoreRingReflection.lean`: printed assembly (later).
   - `def PrintedCoreRingReflection : Prop` + `theorem printedCoreRingReflection`, and one Prop
     per sentence: keys `42c043ef7ab5`, `8981cd70915a`, `43afa4ee3f10`, `cfbacaa0fffa`,
     `9dae685e37b9`, `b23e0f5197b5`.

## Interfaces needed (consumed through owners' interface lemmas, never duplicated)

- chain-core (S1): `R_X`, and restriction `R_X →+* R_Y` as a surjective ring hom (or the carrier
  to build it); LEF ⇒ stably finite; a unital hom into a directly finite ring kills every `d` of
  `eq:clopen-defect-pair`.
- chain-matricial (S5): `lem:transient-matrices`, i.e. the kernel of restriction is `I`, and `I` is generated
  as a two-sided ideal by the defects; `I = LC_c(X∖Y,k) ⋊ ℤ`, so `I = 0 ⇔ X = Y`.
- chain-itinerary (S4) / `lem:chain-core-models`: `R_Y` is LEF.

## Residuals (named, model-tested hypothesis Props until the owner lands)

| Prop (planned name) | content | owner |
|---|---|---|
| `LEFStablyFiniteInterface` | `IsLEFRing A → IsStablyFiniteRing A` | chain-core S1 |
| `DefectKilledInterface` | unital hom `R_X → A`, `A` directly finite, kills each `d` | chain-core S1 |
| `TransientKernelInterface` | `ker(R_X → R_Y) = I = ⟨defects⟩` | chain-matricial S5 |
| `CoreRingLEFInterface` | `IsLEFRing R_Y` | chain-itinerary S4 |
| `TransientIdealBotInterface` | `I = ⊥ ⇔ X = Y` | chain-matricial S5 |

## Infra

- No `$NM/lanes/chain-reflection.clone` yet; asked main for a clone assignment.

## Status

- Step 1 (plan) landed with this file. Next: `DirectlyFiniteCorner.lean` → probe → land on GREEN →
  queue wiring.
