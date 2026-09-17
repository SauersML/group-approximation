import GroupApproximation.Manuscript.NonMFSentences.CoreRingReflectionProofClosed
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:core-ring-reflection`, proof: amplification to `M_m`

`non_mf_groups_exist.tex`, proof of Theorem `thm:core-ring-reflection` (tex 1527–1537):

> Now let $\varphi\colon M_m(R_X)\to A$ be unital with $A$ directly finite.  The corner
> $\varphi(E_{11})A\varphi(E_{11})$ is directly finite.  Apply the preceding argument to the unital
> map $r\mapsto\varphi(rE_{11})$ into this corner.  Multiplication by the other matrix units shows
> that $\varphi$ kills $M_m(I)$.  Its quotient $M_m(R_Y)$ is LEF, as follows entrywise from finite
> ring tables.

Objects: `R_X = ClopenCrossedProduct T k`, `Y = CR(T)` (`Dynamics.chainRecurrentSet T`),
`R_Y = ClopenCrossedProduct (restrictHomeo T (image_core T)) k`, and
`I = ClopenCrossedProduct.transientIdeal T k (image_core T) = ker (R_X → R_Y)`.

Proof route (nothing assumed):
* "the preceding argument" is `CoreRingReflection.killsKernelOfDirectlyFinite_coreRestrict`: every
  unital map from `R_X` into a directly finite ring kills `I`.  It is applied to
  `matrixUnitCornerHom φ i : r ↦ φ(r E_ii)`, whose target `Corner A (φ E_ii)` is directly finite
  (instance `isDedekindFiniteMonoid_corner`).
* "multiplication by the other matrix units" is `map_eq_zero_of_forall_entry_mem`
  (`E_ij x = E_ii x · E_ij`, summed over entries).
* "entrywise from finite ring tables" is `Pestov91.IsLEFRing.matrix` applied to
  "`R_Y` is LEF" (`ChainCore.coreModelsLEFStatement`, closed).

Endpoints:
* `manuscriptSentence_applyPrecedingArgumentToCornerMap` (tex 1534–1535);
* `manuscriptSentence_matrixUnitsKillMatrixIdeal` (tex 1535–1536);
* `manuscriptSentence_matrixQuotientIsLEF` (tex 1536–1537).

The printed `E_11` is the case `i = 0` of the statements below, which hold for every diagonal unit.
-/

universe w

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace ChainB

open MFQuotientUnits

/-- **"Apply the preceding argument to the unital map $r\mapsto\varphi(rE_{11})$ into this corner"**
(tex 1534–1535).  For every unital `φ : M_m(R_X) → A` with `A` directly finite and every index `i`:
the corner at `φ(E_ii)` is directly finite, the map `r ↦ φ(r E_ii)` is a unital ring homomorphism
into it (`matrixUnitCornerHom φ i`), and this map kills `I = ker (R_X → R_Y)`. -/
theorem manuscriptSentence_applyPrecedingArgumentToCornerMap
    {X : Type} [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] (T : X ≃ₜ X)
    (k : Type) [Field k] (m : ℕ) (A : Type w) [Ring A] [IsDedekindFiniteMonoid A]
    (φ : Matrix (Fin m) (Fin m) (ClopenCrossedProduct T k) →+* A) (i : Fin m) :
    IsDedekindFiniteMonoid
        (Corner A (φ (Matrix.single i i 1)) (isIdempotentElem_map_single_one φ i)) ∧
      (∀ r : ClopenCrossedProduct T k,
        ((matrixUnitCornerHom φ i r : Corner A _ _) : A) = φ (Matrix.single i i r)) ∧
      ∀ x ∈ ClopenCrossedProduct.transientIdeal T k
          (GroupApproximation.ChainCore.DynamicRankBudget.image_core T),
        matrixUnitCornerHom φ i x = 0 := by
  refine ⟨inferInstance, fun r => coe_matrixUnitCornerHom φ i r, fun x hx => ?_⟩
  exact GroupApproximation.ChainCore.CoreRingReflection.killsKernelOfDirectlyFinite_coreRestrict.{w}
    T k _ (matrixUnitCornerHom φ i) x
    ((ClopenCrossedProduct.mem_transientIdeal T k
      (GroupApproximation.ChainCore.DynamicRankBudget.image_core T)).1 hx)

/-- **"Multiplication by the other matrix units shows that $\varphi$ kills $M_m(I)$"**
(tex 1535–1536).  Every unital `φ : M_m(R_X) → A` into a directly finite ring vanishes on every
matrix all of whose entries lie in `I = ker (R_X → R_Y)`. -/
theorem manuscriptSentence_matrixUnitsKillMatrixIdeal
    {X : Type} [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] (T : X ≃ₜ X)
    (k : Type) [Field k] (m : ℕ) (A : Type w) [Ring A] [IsDedekindFiniteMonoid A]
    (φ : Matrix (Fin m) (Fin m) (ClopenCrossedProduct T k) →+* A)
    (M : Matrix (Fin m) (Fin m) (ClopenCrossedProduct T k))
    (hM : ∀ i j, M i j ∈ ClopenCrossedProduct.transientIdeal T k
      (GroupApproximation.ChainCore.DynamicRankBudget.image_core T)) :
    φ M = 0 := by
  refine map_eq_zero_of_forall_entry_mem
    (I := {x | GroupApproximation.ChainCore.DynamicRankBudget.coreRestrict T k x = 0}) ?_ φ M ?_
  · intro B _ _ ψ x hx
    exact GroupApproximation.ChainCore.CoreRingReflection.killsKernelOfDirectlyFinite_coreRestrict.{w}
      T k B ψ x hx
  · intro i j
    exact (ClopenCrossedProduct.mem_transientIdeal T k
      (GroupApproximation.ChainCore.DynamicRankBudget.image_core T)).1 (hM i j)

/-- **"Its quotient $M_m(R_Y)$ is LEF, as follows entrywise from finite ring tables"**
(tex 1536–1537), for `X` a nonempty compact totally disconnected metric space, `T` a homeomorphism,
`k` a finite field and `Y = CR(T)`. -/
theorem manuscriptSentence_matrixQuotientIsLEF
    (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] [Nonempty X]
    (T : X ≃ₜ X) (k : Type) [Field k] [Finite k] (m : ℕ) :
    GroupApproximation.Pestov91.IsLEFRing (Matrix (Fin m) (Fin m)
      (ClopenCrossedProduct
        (ClopenCrossedProduct.restrictHomeo T
          (GroupApproximation.ChainCore.DynamicRankBudget.image_core T)) k)) :=
  (GroupApproximation.ChainCore.coreModelsLEFStatement X T k).matrix (Fin m)

end ChainB
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.ChainB.manuscriptSentence_applyPrecedingArgumentToCornerMap
#audit_axioms GroupApproximation.Manuscript.NonMF.ChainB.manuscriptSentence_matrixUnitsKillMatrixIdeal
#audit_axioms GroupApproximation.Manuscript.NonMF.ChainB.manuscriptSentence_matrixQuotientIsLEF
