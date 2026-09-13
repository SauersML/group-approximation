# Lane chain-itinerary: sec:chain-core S4, the general-X case of lem:chain-core-models

Snapshot: origin/main 3d9b2c4f0 (09-13).  Scope report: `notes/nm-swarm/reports/chain-core.md`, item S4.
Tex: `non_mf_groups_exist.tex` lines 1428–1462 (proof of lem:chain-core-models, "For general $X$" through
"forces $d|_Y=0$"), plus the statement row `d8e1a694d87c` (line 1372: nonempty; `R_Y` LEF).
Probe clone: `stw-fix` (shared, assigned by main 09-13).

## Keys owned

| key | tex | sentence (abridged) | carrier (landed SHA, or planned) |
|---|---|---|---|
| `3d8a2204752a` | 1428 | refining finite clopen partitions with mesh → 0 | `ChainCore.exists_refiningClopenPartitions` (3d9b2c4f0) |
| `fe2bd83087c0` | 1429 | itinerary subshifts `π_m`, cores `Y_m`, one-block factors `ρ_lm` | `ChainCore.itinerary`, `itinerarySubshift`, `oneBlock` (probing) |
| `4bb19e581840` | 1432 | one-block factors preserve the cycle condition | planned `oneBlock_image_cycleCondition` (needs chain-words' predicate) |
| `ed348643e2ad` | 1433 | `ρ_lm(Y_l) ⊆ Y_m`, the display for `Y_*` | `ChainCore.inverseLimitCore`, `preimage_itinerary_antitone` (written) |
| `807793f12a5e` | 1439 | `π_m(Y_*) = ⋂_{l≥m} ρ_lm(Y_l)` by compactness in the fibers | `ChainCore.itinerary_image_inverseLimitCore` (written) |
| `b180421b55ab` | 1439 | the intersection satisfies the cycle condition | planned `cycleCondition_itinerary_image_generalCore` |
| `2df08eeac3cb` | 1442 | coefficient pullback injective unital; LC functions constant on a fine partition | `Pestov91.CrossedProduct.coeffMap`, `coeffMap_injective` (f9390d923); `ChainCore.exists_forall_proj_eq_imp_of_locallyConstant` (3d9b2c4f0) |
| `c825bc73828a` | 1444 | `R_{Y_*}` is an increasing union of LEF rings, so LEF | `Pestov91.isLEFRing_of_monotone_subrings`, `isLEFRing_of_monotone_ringHom_range` (6ac372c36); planned `isLEFRing_crossedProduct_generalCore` |
| `e6626f95fede` `2583cbd0c0f2` `3b218f92cd81` `fb195144e5c2` `8921296d639a` | 1447 | `Y ⊆ Y_*`; `Y_* ⊆ Y` by lifting a closed chain; `Y_* = Y` | planned `generalCore_subset_chainRecurrentSet`, `generalCore_eq_chainRecurrentSet` |
| `042966c81c7e` | 1456 | pulled-back symbolic defects cover `X∖Y` | planned `exists_defect_translate_of_not_mem_chainRecurrentSet` |
| `d8e1a694d87c` (rest) | 1372 | `Y` nonempty; `R_Y` LEF | planned `chainRecurrentSet_nonempty`, `isLEFRing_crossedProduct_chainRecurrentSet` |

Census rows: `metadata/nm-census-rows/chain-itinerary.tsv` (`3d8a2204752a` formalized; `c825bc73828a`,
`2df08eeac3cb` partial).

## Modules (unwired; each small, probed and landed separately)

1. `GroupApproximation/Algebra/LEFRingDirectedUnion.lean`: **LANDED 6ac372c36**, probe 0913-155051-83464 GREEN.
   Namespace `GroupApproximation.Pestov91`: `IsLEFRing.of_injective`, `isLEFRing_of_forall_finset_subset_range`,
   `isLEFRing_of_monotone_ringHom_range`, `isLEFRing_of_monotone_subrings`.  chain-reflection consumes
   `IsLEFRing.of_injective` from here (main's ruling).
2. `GroupApproximation/Algebra/SkewMonoidAlgebraCoefficientMap.lean`: **LANDED f9390d923**, probe
   0913-155549-37754 GREEN.  Namespace `GroupApproximation.Pestov91.CrossedProduct`, any monoid `G`:
   `coeffMap φ hφ : SkewMonoidAlgebra A G →+* SkewMonoidAlgebra B G`, `coeffMap_apply`, `coeffMap_single`,
   `coeff_coeffMap`, `coeffMap_injective`, `coeffMap_surjective`, `coeffMap_C`.
3. `GroupApproximation/Dynamics/RefiningClopenPartitions.lean`: **LANDED 3d9b2c4f0**, probe 0913-161748-63962
   GREEN.  Namespace `GroupApproximation.ChainCore`: `structure IsRefiningClopenPartitions S` (`antitone`,
   `mesh_lt`), `proj_eq_of_le`, `exists_discreteQuotient_mesh_lt`, `exists_refiningClopenPartitions`,
   `exists_forall_proj_eq_imp_of_locallyConstant`.
4. `GroupApproximation/Dynamics/ItinerarySubshift.lean` (probing).  `itinerary T S x i = S.proj ((T ^ i) x)`,
   `continuous_itinerary`, `itinerary_zpow_apply` (`π ∘ T^n = shift n ∘ π`), `itinerary_apply_self`,
   `itinerarySubshift`, `isClosed_itinerarySubshift`, `mapsTo_shift_itinerarySubshift`, `oneBlock`,
   `continuous_oneBlock`, `oneBlock_shift`, `oneBlock_oneBlock`, `oneBlock_itinerary`,
   `oneBlock_image_itinerarySubshift`.
5. `GroupApproximation/Dynamics/ItineraryInverseLimit.lean` (written, probe after 4).  For a closed family
   `Y m ⊆ itinerarySubshift T (S m)` with `oneBlock (hS h) '' Y l ⊆ Y m`: `inverseLimitCore T Y = ⋂ m, π_m⁻¹(Y m)`,
   `mem_inverseLimitCore`, `isClosed_inverseLimitCore`, `itinerary_mem_of_le`, `preimage_itinerary_antitone`,
   `itinerary_image_inverseLimitCore` (`π_m(Y_*) = ⋂_{l≥m} ρ_lm(Y_l)`), `inverseLimitCore_nonempty`,
   `mapsTo_zpow_inverseLimitCore`.
6. `GroupApproximation/Dynamics/ChainCoreGeneral.lean` (after S1, S2, S3): instantiate 5 with the cores, the cycle
   condition `b180421b55ab`, `R_{Y_*}` LEF, `Y_* = Y`, the defect cover.  It needs the fine-partition lemma on the
   subspace `Y_*`, via `DiscreteQuotient.comap` along `Subtype.val`.

## Interfaces found

- chain-core (S1): `GroupApproximation.ClopenCrossedProduct T k` (`T : X ≃ₜ X`), `ClopenCoeff`,
  `ClopenCrossedProduct.coeff`; defects `defectP`, `defectD` (`Dynamics/ClopenDefectPair.lean`).  Restriction, the
  one definition of `R_X → R_Y` (lead ruling 09-13 16:20): `ClopenCrossedProduct.restrict T k hY :
  ClopenCrossedProduct T k →+* ClopenCrossedProduct (restrictHomeo T hY) k` for `hY : T '' Y = Y`, with
  `restrict_coeff`, `restrict_unit` (`Dynamics/ClopenCrossedProductComap.lean`, landing next).
- hull-euler (S2), landed 20911e5b2: `GroupApproximation.Dynamics.chainRecurrentSet (T : X → X)` over a
  `UniformSpace`, `isClosed_chainRecurrentSet`, `image_chainRecurrentSet (T : X ≃ₜ X) : T '' chainRecurrentSet T =
  chainRecurrentSet T`, `mapsTo_chainRecurrentSet (hπ : Continuous π) (h : Function.Semiconj π T S)`.
- chain-words (S3a), on origin: `GroupApproximation.WordGraph.CycleCondition (X : Set (ℤ → A))`; subshifts are
  plain sets with `∀ n : ℤ, Set.MapsTo (shift n) X X`.  Planned `isLEFRing_skewMonoidAlgebra_of_cycleCondition`
  (`Dynamics/SubshiftCycleLEF.lean`) takes `K : Type` with `[Ring K] [Finite K]` and a finite alphabet.
- chain-subshift (S3b), on origin: `ChainCore.nonempty_iInter_of_antitone`, `image_iInter_eq_iInter_image_of_antitone`
  (`Dynamics/SubshiftLanguageStabilization.lean`); `Dynamics/RetainedSubshift.lean`.  The core `Y_0` is not yet
  named.

Module 6 takes each missing input as a named, model-tested hypothesis Prop and lists it below as a residual.

## Residual Props

None yet.

## Follow-ups

- The docstrings of modules 1 and 2 cite tex line 1437; the sentences are at lines 1442–1445.

## Progress log

- 09-13 15:30: plan landed (this file).  Blocker: no probe clone.
- 09-13 15:50: clone `stw-fix` assigned.  LEFRingDirectedUnion GREEN 0913-155051-83464, landed 6ac372c36;
  chain-reflection sent the module name.
- 09-13 15:55: SkewMonoidAlgebraCoefficientMap GREEN 0913-155549-37754, landed f9390d923.  Both queued in
  `wire-queue.txt`.
- 09-13 16:04: RefiningClopenPartitions probe 0913-160442-90577 FAILED: `Mathlib.Topology.MetricSpace.Basic` was not
  imported, so autoImplicit bound `MetricSpace` as a variable.  Fixed (import added; the predicate is now a
  structure).  ItinerarySubshift written.
- 09-13 16:09: probe 0913-160924-21796 FAILED: `Nat.one_div_pos_of_nat` does not exist at the pin; replaced by
  `positivity`.  Tex line citations corrected (1428–1429, 1443–1444).
- 09-13 16:17: RefiningClopenPartitions GREEN 0913-161748-63962, landed 3d9b2c4f0, queued for wiring.
  ItinerarySubshift probing; ItineraryInverseLimit written.  chain-reflection told the `R_Y` spelling:
  the codomain of `ClopenCrossedProduct.restrict`.
