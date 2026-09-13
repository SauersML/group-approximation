# Lane chain-itinerary: sec:chain-core S4, the general-X case of lem:chain-core-models

Snapshot: origin/main 527ddbf89 (09-13).  Scope report: `notes/nm-swarm/reports/chain-core.md`, item S4.
Tex: `non_mf_groups_exist.tex` lines 1426–1459 (proof of lem:chain-core-models, "For general $X$" through
"forces $d|_Y=0$"), plus the statement row `d8e1a694d87c` (nonempty; `R_Y` LEF).

## Keys owned

| key | tex | sentence (abridged) | planned carrier |
|---|---|---|---|
| `3d8a2204752a` | 1426 | refining finite clopen partitions with mesh → 0 | `exists_refiningClopenPartitions` |
| `fe2bd83087c0` | 1426 | itinerary subshifts `π_m`, cores `Y_m`, one-block factors `ρ_lm` | `itinerary`, `itinerarySubshift`, `oneBlock` |
| `4bb19e581840` | 1426 | one-block factors preserve the cycle condition | `oneBlock_image_cycleCondition` (needs chain-words' predicate) |
| `ed348643e2ad` | 1426 | `ρ_lm(Y_l) ⊆ Y_m`, the display for `Y_*` | `oneBlock_image_core_subset`, `generalCore` |
| `807793f12a5e` | 1437 | `π_m(Y_*) = ⋂_{l≥m} ρ_lm(Y_l)` by compactness in the fibers | `itinerary_image_generalCore` |
| `b180421b55ab` | 1437 | the intersection satisfies the cycle condition | `cycleCondition_itinerary_image_generalCore` |
| `2df08eeac3cb` | 1437 | coefficient pullback injective unital; LC functions factor through a fine partition | `CrossedProduct.coeffMap`, `coeffMap_injective`, `exists_factor_of_locallyConstant` |
| `c825bc73828a` | 1437 | `R_{Y_*}` is an increasing union of LEF rings, so LEF | `isLEFRing_of_monotone_subrings`, `isLEFRing_crossedProduct_generalCore` |
| `e6626f95fede` `2583cbd0c0f2` `3b218f92cd81` `fb195144e5c2` `8921296d639a` | 1445 | `Y_* ⊆ Y` by lifting a closed chain; `Y_* = Y` | `generalCore_subset_chainRecurrentSet`, `generalCore_eq_chainRecurrentSet` |
| `042966c81c7e` | 1454 | pulled-back symbolic defects cover `X∖Y` | `exists_defect_translate_of_not_mem_chainRecurrentSet` |
| `d8e1a694d87c` (rest) | 1370 | `Y` nonempty; `R_Y` LEF | `chainRecurrentSet_nonempty`, `isLEFRing_crossedProduct_chainRecurrentSet` |

## Planned modules (unwired; each small, probed and landed separately)

1. `GroupApproximation/Algebra/LEFRingDirectedUnion.lean` (no upstream).  Namespace `GroupApproximation.Pestov91`.
   - `IsLEFRing.of_injective (hB : IsLEFRing B) (φ : A →+* B) (hφ : Injective φ) : IsLEFRing A`
   - `isLEFRing_of_forall_finset_subset_range`: every finite subset lies in the range of an injective ring hom
     from an LEF ring ⇒ LEF
   - `isLEFRing_of_monotone_subrings (B : ℕ → Subring A) (hB : Monotone B) (hcover : ∀ a, ∃ m, a ∈ B m)
     (hLEF : ∀ m, IsLEFRing (B m)) : IsLEFRing A` (printed: an increasing union of LEF rings is LEF)
2. `GroupApproximation/Algebra/SkewMonoidAlgebraCoefficientMap.lean` (no upstream).
   Namespace `GroupApproximation.Pestov91.CrossedProduct`, for any monoid `G` acting on rings `A`, `B`.
   - `coeffMap (φ : A →+* B) (hφ : ∀ g a, φ (g • a) = g • φ a) : SkewMonoidAlgebra A G →+* SkewMonoidAlgebra B G`
   - `coeff_coeffMap`, `coeffMap_single`, `coeffMap_C`, `coeffMap_injective`, `coeffMap_surjective`, `coeffMap_comp`
   - The restriction `R_X → R_Y` of lem:transient-matrices is the same construction (chain-matricial may consume it).
3. `GroupApproximation/Dynamics/RefiningClopenPartitions.lean` (no upstream).  Namespace `GroupApproximation.ChainCore`.
   - `IsRefiningClopenPartitions (S : ℕ → DiscreteQuotient X)`: `Antitone S` and mesh → 0 for the metric
     (the atoms are finite in number by Mathlib's `DiscreteQuotient` instance on compact spaces)
   - `exists_refiningClopenPartitions [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X]`
   - `exists_factor_of_locallyConstant`: a locally constant function is constant on the atoms of some `S m`
     (Lebesgue number of its fibre cover)
4. `GroupApproximation/Dynamics/ItinerarySubshift.lean` (no upstream).
   - `itinerary T S : X → ℤ → S`, `x ↦ (i ↦ S.proj ((T ^ i) x))`; `continuous_itinerary`; `itinerary_homeo`
     (`π ∘ T = σ ∘ π`)
   - `itinerarySubshift T S`, closed and shift-invariant (the carrier of a Mathlib `Subshift S ℤ` if chain-words
     uses that structure)
   - `oneBlock (h : S ≤ S') : (ℤ → S) → (ℤ → S')`; `oneBlock_itinerary`; `oneBlock_shift`; `continuous_oneBlock`
5. `GroupApproximation/Dynamics/ChainCoreGeneral.lean` (after S1, S2, S3).
   - `generalCore T S := ⋂ m, itinerary T (S m) ⁻¹' core (itinerarySubshift T (S m))`
   - the image identity `807793f12a5e`, the cycle condition `b180421b55ab`, `R_{Y_*}` LEF, `Y_* = Y`, the defect cover.

## Interfaces needed (from each owner's report, when landed)

- chain-core (S1): the coefficient ring `LC(X,k)` with the `ℤ`-action of `T` and the name of `R_X`.
- hull-euler (S2): `CR(T)` (`chainRecurrentSet`) and its metric setting; chain recurrence passes to factors.
- chain-words (S3a): the subshift representation, the cycle-condition predicate, cycle condition ⇒ LEF crossed product.
- chain-subshift (S3b): `Y_0` (`core`), `Y_0 = CR(σ)`, language stabilization for decreasing cycle-condition
  subshifts, noncyclic edge ⇒ forward-closed `P` with `Tx ∈ P∖T(P)`.

Until they land, module 5 takes each as a named, model-tested hypothesis Prop and lists it here as a residual.

## Residual Props

None yet.

## Progress log

- 09-13 15:30: plan landed (this file).  Modules 1–4 have no upstream dependency; starting with 1 and 2.
  Blocker for probing: no probe clone is assigned to this lane (`lanes/chain-itinerary.clone` absent).
