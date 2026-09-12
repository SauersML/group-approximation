import GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationGeneratedRestrictionCore

/-!
# Separability of the tensor-synchronized generated algebra
-/

namespace GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationAssembly

open HNNCoronaConjugatorSentenceAudit
open TensorSynchronizationMatrixCore
open PolarLiftingGeneralCStar Filter

noncomputable section

universe u w

noncomputable local instance tensorGeneratedSeparablePartialOrder
    (A : Type*) [CStarAlgebra A] : PartialOrder A :=
  CStarAlgebra.spectralOrder A

local instance tensorGeneratedSeparableStarOrderedRing
    (A : Type*) [CStarAlgebra A] : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

/-- The synchronized generated algebra is separable for countable input
groups, independently of any MF permanence theorem. -/
theorem synchronizedGeneratedCStar_separable
    {G : Type w} [Countable G] {D : Type u} [CStarAlgebra D]
    (rho : G → unitary D) :
    TopologicalSpace.SeparableSpace (SynchronizedGeneratedCStar rho) := by
  let s : Set D := Set.range fun g : G ↦ (rho g : D)
  have hs : s.Countable := Set.countable_range _
  have hsStar : (star s : Set D).Countable := by
    rw [← Set.image_star]
    exact hs.image _
  let t : Set D := s ∪ star s
  have ht : t.Countable := by
    simpa [t] using hs.union hsStar
  letI : Countable ↑t := ht.to_subtype
  have hmonoid :
      ((Submonoid.closure t : Submonoid D) : Set D).Countable := by
    rw [Submonoid.closure_eq_mrange, MonoidHom.coe_mrange]
    exact Set.countable_range _
  have hadjoin : TopologicalSpace.IsSeparable
      ((StarAlgebra.adjoin ℂ s : StarSubalgebra ℂ D) : Set D) := by
    change TopologicalSpace.IsSeparable
      ((StarAlgebra.adjoin ℂ s).toSubalgebra.toSubmodule : Set D)
    rw [StarAlgebra.adjoin_eq_span]
    simpa [t] using hmonoid.isSeparable.span
  have hclosed : TopologicalSpace.IsSeparable
      ((SynchronizedGeneratedCStar rho : StarSubalgebra ℂ D) : Set D) := by
    change TopologicalSpace.IsSeparable
      (((StarAlgebra.adjoin ℂ s).topologicalClosure :
        StarSubalgebra ℂ D) : Set D)
    rw [StarSubalgebra.topologicalClosure_coe]
    exact hadjoin.closure
  exact hclosed.separableSpace

end

end GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationAssembly
