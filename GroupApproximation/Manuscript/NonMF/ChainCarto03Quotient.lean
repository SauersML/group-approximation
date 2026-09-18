import GroupApproximation.Manuscript.NonMFSentences.CoreRingReflectionProofClosed
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:core-ring-reflection`, amplification: `M_m(R_Y)` is the quotient by `M_m(I)`, and is LEF

`non_mf_groups_exist.tex`, proof of Theorem `thm:core-ring-reflection` (tex 1531–1537):

> For amplification, let $\varphi\colon M_m(R_X)\to A$ be unital with $A$ directly finite, and put
> $e=\varphi(E_{11})$.  [...]  Apply the preceding argument to the unital map
> $r\mapsto\varphi(rE_{11})$ into this corner.  Multiplication by the other matrix units shows that
> $\varphi$ kills $M_m(I)$.  Its quotient $M_m(R_Y)$ is LEF, as follows entrywise from finite ring
> tables.

## Carto re-audit (lane nm-chain-03)

The three endpoints of `Manuscript/NonMF/ChainB/CoreRingReflectionAmplification.lean`
(`manuscriptSentence_applyPrecedingArgumentToCornerMap`,
`manuscriptSentence_matrixUnitsKillMatrixIdeal`,
`manuscriptSentence_matrixQuotientIsLEF`) were re-read against the built corpus: every name
resolves (`isIdempotentElem_map_single_one`, `matrixUnitCornerHom`, `coe_matrixUnitCornerHom`,
`isDedekindFiniteMonoid_corner`, `map_eq_zero_of_forall_entry_mem` in
`Algebra/DirectlyFiniteCorner`; `CoreRingReflection.killsKernelOfDirectlyFinite_coreRestrict`;
`ClopenCrossedProduct.transientIdeal`, `mem_transientIdeal` in `Dynamics/TransientIdealExact`;
`ChainCore.coreModelsLEFStatement`; `Pestov91.IsLEFRing.matrix`), the matrix unit is
`Matrix.single` (the v4.32.0 name, not the deprecated `stdBasisMatrix`), and the proof terms are
the ones of the built `CoreRingReflectionProofClosed`.  No
statement is false and no hypothesis beyond the printed setting is taken.

One fidelity nit: the printed "Its quotient $M_m(R_Y)$" identifies `M_m(R_Y)` as the quotient of
`M_m(R_X)` by `M_m(I)`, while `ChainB.manuscriptSentence_matrixQuotientIsLEF` only states that
`M_m(R_Y)` is LEF.  This module adds the identification, so that the endpoint
`manuscriptSentence_matrixQuotientIsLEF'` states the whole sentence:

* `mapMatrix_coreRestrict_surjective`: `M_m(R_X) → M_m(R_Y)` is onto (entrywise surjectivity of the
  core restriction, `CoreRingReflection.coreRestrict_surjective`, through
  `mapMatrix_surjective_of_surjective`);
* `mapMatrix_coreRestrict_eq_zero_iff`: its kernel is `M_m(I)`, the matrices with all entries in
  `I = ker (R_X → R_Y)` (`mapMatrix_eq_zero_iff` and `mem_transientIdeal`);
* `M_m(R_Y)` is LEF (`coreModelsLEFStatement`, entrywise by `Pestov91.IsLEFRing.matrix`).

Setting (sec:chain-core): `X` a nonempty compact totally disconnected metric space, `T : X ≃ₜ X`,
`k` a finite field, `Y = CR(T)`.  The printed `m ≥ 1` is not needed: all statements hold for every
`m : ℕ`.
-/

namespace GroupApproximation.Manuscript.NonMF.ChainCarto03

/-- A matrix lies in the kernel of `f.mapMatrix` exactly when all its entries lie in `ker f`. -/
theorem mapMatrix_eq_zero_iff {R S : Type*} [Ring R] [Ring S] (n : Type*) [Fintype n]
    [DecidableEq n] (f : R →+* S) (M : Matrix n n R) :
    f.mapMatrix M = 0 ↔ ∀ i j, f (M i j) = 0 := by
  constructor
  · intro h i j
    simpa using congrArg (fun N => N i j) h
  · intro h
    ext i j
    simpa using h i j

#audit_axioms GroupApproximation.Manuscript.NonMF.ChainCarto03.mapMatrix_eq_zero_iff

/-- `M_m(R_X) → M_m(R_Y)`, entrywise core restriction, is onto. -/
theorem mapMatrix_coreRestrict_surjective
    {X : Type} [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] (T : X ≃ₜ X)
    (k : Type) [Field k] (m : ℕ) :
    Function.Surjective
      ((GroupApproximation.ChainCore.DynamicRankBudget.coreRestrict T k).mapMatrix :
        Matrix (Fin m) (Fin m) (GroupApproximation.ClopenCrossedProduct T k) →+* _) :=
  GroupApproximation.mapMatrix_surjective_of_surjective (Fin m)
    (GroupApproximation.ChainCore.DynamicRankBudget.coreRestrict T k)
    (GroupApproximation.ChainCore.CoreRingReflection.coreRestrict_surjective T k)

#audit_axioms GroupApproximation.Manuscript.NonMF.ChainCarto03.mapMatrix_coreRestrict_surjective

/-- The kernel of `M_m(R_X) → M_m(R_Y)` is `M_m(I)`: a matrix restricts to zero exactly when all of
its entries lie in the transient ideal `I = ker (R_X → R_Y)`. -/
theorem mapMatrix_coreRestrict_eq_zero_iff
    {X : Type} [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] (T : X ≃ₜ X)
    (k : Type) [Field k] (m : ℕ)
    (M : Matrix (Fin m) (Fin m) (GroupApproximation.ClopenCrossedProduct T k)) :
    (GroupApproximation.ChainCore.DynamicRankBudget.coreRestrict T k).mapMatrix M = 0 ↔
      ∀ i j, M i j ∈ GroupApproximation.ClopenCrossedProduct.transientIdeal T k
        (GroupApproximation.ChainCore.DynamicRankBudget.image_core T) :=
  (mapMatrix_eq_zero_iff (Fin m)
      (GroupApproximation.ChainCore.DynamicRankBudget.coreRestrict T k) M).trans
    (forall_congr' fun i => forall_congr' fun j =>
      (GroupApproximation.ClopenCrossedProduct.mem_transientIdeal T k
        (GroupApproximation.ChainCore.DynamicRankBudget.image_core T)).symm)

#audit_axioms GroupApproximation.Manuscript.NonMF.ChainCarto03.mapMatrix_coreRestrict_eq_zero_iff

/-- **"Its quotient $M_m(R_Y)$ is LEF, as follows entrywise from finite ring tables"** (tex
1536–1537), with the quotient identification printed by "Its quotient": entrywise restriction
`M_m(R_X) → M_m(R_Y)` is onto, its kernel is `M_m(I)` (all entries in `I = ker (R_X → R_Y)`), and
`M_m(R_Y)` is an LEF ring.  Supersedes `ChainB.manuscriptSentence_matrixQuotientIsLEF`, which is the
third conjunct. -/
theorem manuscriptSentence_matrixQuotientIsLEF'
    (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] [Nonempty X]
    (T : X ≃ₜ X) (k : Type) [Field k] [Finite k] (m : ℕ) :
    Function.Surjective
        ((GroupApproximation.ChainCore.DynamicRankBudget.coreRestrict T k).mapMatrix :
          Matrix (Fin m) (Fin m) (GroupApproximation.ClopenCrossedProduct T k) →+* _) ∧
      (∀ M : Matrix (Fin m) (Fin m) (GroupApproximation.ClopenCrossedProduct T k),
        (GroupApproximation.ChainCore.DynamicRankBudget.coreRestrict T k).mapMatrix M = 0 ↔
          ∀ i j, M i j ∈ GroupApproximation.ClopenCrossedProduct.transientIdeal T k
            (GroupApproximation.ChainCore.DynamicRankBudget.image_core T)) ∧
      GroupApproximation.Pestov91.IsLEFRing (Matrix (Fin m) (Fin m)
        (GroupApproximation.ClopenCrossedProduct
          (GroupApproximation.ClopenCrossedProduct.restrictHomeo T
            (GroupApproximation.ChainCore.DynamicRankBudget.image_core T)) k)) :=
  ⟨mapMatrix_coreRestrict_surjective T k m, mapMatrix_coreRestrict_eq_zero_iff T k m,
    (GroupApproximation.ChainCore.coreModelsLEFStatement X T k).matrix (Fin m)⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.ChainCarto03.manuscriptSentence_matrixQuotientIsLEF'

end GroupApproximation.Manuscript.NonMF.ChainCarto03
