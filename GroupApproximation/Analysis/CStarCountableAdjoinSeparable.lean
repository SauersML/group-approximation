import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Metrizable.Basic

/-!
# Separability of a countably generated closed C-star algebra
-/

namespace GroupApproximation

noncomputable section

universe w

/-- A countable set generates a separable closed star subalgebra. -/
theorem topologicalClosure_adjoin_separable_of_countable
    {D : Type w} [CStarAlgebra D] (t : Set D) (ht : t.Countable) :
    TopologicalSpace.SeparableSpace
      (StarAlgebra.adjoin ℂ t).topologicalClosure := by
  let tStar : Set D := t ∪ star t
  have htStar : tStar.Countable := by
    have hstar : (star t : Set D).Countable := by
      rw [← Set.image_star]
      exact ht.image _
    exact ht.union hstar
  letI : Countable ↑tStar := htStar.to_subtype
  have hmonoid :
      ((Submonoid.closure tStar : Submonoid D) : Set D).Countable := by
    rw [Submonoid.closure_eq_mrange, MonoidHom.coe_mrange]
    exact Set.countable_range _
  have hadjoin : TopologicalSpace.IsSeparable
      ((StarAlgebra.adjoin ℂ t : StarSubalgebra ℂ D) : Set D) := by
    change TopologicalSpace.IsSeparable
      ((StarAlgebra.adjoin ℂ t).toSubalgebra.toSubmodule : Set D)
    rw [StarAlgebra.adjoin_eq_span]
    simpa [tStar] using hmonoid.isSeparable.span
  exact hadjoin.closure.separableSpace

end

end GroupApproximation
