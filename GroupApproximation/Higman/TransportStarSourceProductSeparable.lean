import GroupApproximation.Higman.ProfiniteBenignProductSeparable
import GroupApproximation.Higman.ConjugatorGraphProfinite

/-!
# The source product separated at the TransportStar intersection

The source-side product introduced by intersecting the conjugator graph with
a first-coordinate condition has a particularly simple finite detector.  If
the first-coordinate subgroup lies in the conjugate-basis range, every factor
in the product is killed by `retK ∘ fst`; a point outside the product has a
nontrivial `retK` coordinate and is detected in a finite quotient of `K`.
-/

namespace GroupApproximation
namespace Higman
namespace TransportStarSourceProductSeparable

noncomputable section

open scoped Pointwise
open Conj

/-- The exact source-product condition needed at the special `hgamma` Inf
stage. -/
theorem graph_mul_fstComap
    (H : Subgroup F₃) (hH : H ≤ cbHom.range) :
    SetProductSeparable Star.graphSub
      (H.comap (MonoidHom.fst F₃ F₃)) := by
  intro x hx
  have hret : Coord.retK x.1 ≠ 1 := by
    intro hret
    have hxrange : x.1 ∈ cbHom.range := by
      rw [← Coord.ker_retK_eq_cbHom_range]
      exact MonoidHom.mem_ker.mpr hret
    obtain ⟨w, hw⟩ := hxrange
    apply hx
    refine ⟨Star.graphHom w, Star.mem_graphSub.mpr ⟨w, rfl⟩,
      ((1 : F₃), (Star.evalHom w)⁻¹ * x.2), ?_, ?_⟩
    · apply Subgroup.mem_comap.mpr
      change (1 : F₃) ∈ H
      exact Subgroup.one_mem H
    · apply Prod.ext
      · simpa [Star.graphHom_apply] using hw
      · simp [Star.graphHom_apply]
  obtain ⟨N, hN⟩ :=
    Group.exists_finiteIndexNormalSubgroup_notMem (Coord.retK x.1) hret
  letI := N.isNormal'
  letI := N.isFiniteIndex'
  let Q := F₃ ⧸ N.toSubgroup
  letI : Finite Q := Subgroup.finite_quotient_of_finiteIndex
  let q : F₃ × F₃ →* Q :=
    (QuotientGroup.mk' N.toSubgroup).comp
      (Coord.retK.comp (MonoidHom.fst F₃ F₃))
  refine ⟨Q, inferInstance, inferInstance, q, ?_⟩
  intro hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
  have haRet : Coord.retK a₀.1 = 1 := by
    exact MonoidHom.mem_ker.mp
      (PairedReturnGraphIntersection.graphSub_le_retK_fst_ker ha₀)
  have hbRange : b₀.1 ∈ cbHom.range := hH (Subgroup.mem_comap.mp hb₀)
  have hbRet : Coord.retK b₀.1 = 1 := by
    rw [← Coord.ker_retK_eq_cbHom_range] at hbRange
    exact MonoidHom.mem_ker.mp hbRange
  have hqx : q x = 1 := by
    rw [← hab]
    change QuotientGroup.mk' N.toSubgroup (Coord.retK a₀.1) *
      QuotientGroup.mk' N.toSubgroup (Coord.retK b₀.1) = 1
    simp [haRet, hbRet]
  apply hN
  exact (QuotientGroup.eq_one_iff (Coord.retK x.1)).mp hqx

/-- Instantiation at the literal coordinate subgroup used by TransportStar. -/
theorem graph_mul_coord_fstComap (T : Set ↑K) :
    SetProductSeparable Star.graphSub
      (((Star.coordSub T).map cbHom).comap (MonoidHom.fst F₃ F₃)) := by
  apply graph_mul_fstComap
  rintro _ ⟨w, -, rfl⟩
  exact ⟨w, rfl⟩

end

end TransportStarSourceProductSeparable
end Higman
end GroupApproximation
