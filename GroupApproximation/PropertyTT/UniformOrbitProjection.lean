import GroupApproximation.Kazhdan.HilbertCircumcenter
import GroupApproximation.Kazhdan.KazhdanFixedSpace

/-!
# Uniform orbit bounds control the moving projection

This is the quantitative fixed-point fact used by the rank-four
quasi-cocycle argument.  If the entire orbit of a vector under a subgroup
stays in a ball of radius `A` about that vector, then its orthogonal moving
component has norm at most `A`.
-/

namespace GroupApproximation
namespace KazhdanFixedSpace

open scoped InnerProductSpace

variable {G E : Type*} [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A uniform displacement bound by every member of a subgroup bounds the
orthogonal projection onto the subgroup-moving subspace. -/
theorem norm_subgroupMovingProjection_le_of_uniform_displacement
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) (x : E) {A : ℝ}
    (hdisp : ∀ g : G, g ∈ H → ‖rho g x - x‖ ≤ A) :
    ‖subgroupMovingProjection rho H x‖ ≤ A := by
  let S : Set E := Set.range fun h : H ↦ rho h.1 x
  have hSne : S.Nonempty := by
    refine ⟨x, 1, ?_⟩
    simp
  have hSball : S ⊆ Metric.closedBall x A := by
    rintro y ⟨h, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa only [norm_sub_rev] using hdisp h.1 h.2
  have hSbdd : Bornology.IsBounded S :=
    (Metric.isBounded_closedBall (x := x) (r := A)).subset hSball
  obtain ⟨c, hc, hcUnique⟩ :=
    Circumcenter.existsUnique_center hSne hSbdd
  have hcenterA : Circumcenter.coveringRadius S c ≤ A := by
    rw [hc]
    exact (Circumcenter.chebyshevRadius_le hSne hSbdd x).trans <|
      Circumcenter.coveringRadius_le hSne fun y hy ↦ by
        rcases hy with ⟨h, rfl⟩
        rw [dist_eq_norm]
        simpa only [norm_sub_rev] using hdisp h.1 h.2
  have hxc : dist x c ≤ A := by
    have hxS : x ∈ S := by
      refine ⟨1, ?_⟩
      simp
    rw [dist_comm]
    exact (Circumcenter.dist_le_coveringRadius hSbdd c hxS).trans hcenterA
  have hSinvariant (h : H) : rho h.1 '' S = S := by
    ext y
    constructor
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      refine ⟨h * k, ?_⟩
      simp
    · rintro ⟨k, rfl⟩
      refine ⟨rho (h⁻¹ * k).1 x, ⟨h⁻¹ * k, rfl⟩, ?_⟩
      simp
  have hcFixed : c ∈ fixedSubspace rho H := by
    rw [mem_fixedSubspace_iff]
    intro g hg
    let h : H := ⟨g, hg⟩
    apply hcUnique
    calc
      Circumcenter.coveringRadius S (rho g c) =
          Circumcenter.coveringRadius (rho g '' S) (rho g c) := by
        rw [hSinvariant h]
      _ = Circumcenter.coveringRadius S c :=
        Circumcenter.coveringRadius_image (rho g).isometry S c
      _ = Circumcenter.chebyshevRadius S := hc
  rw [subgroupMovingProjection_eq_sub_fixedProjection]
  let U := fixedSubspace rho H
  letI : CompleteSpace U := (isClosed_fixedSubspace rho H).completeSpace_coe
  change ‖x - U.starProjection x‖ ≤ A
  rw [U.starProjection_minimal]
  calc
    (⨅ y : U, ‖x - y‖) ≤ ‖x - (⟨c, hcFixed⟩ : U)‖ :=
      ciInf_le
        ⟨0, Set.forall_mem_range.mpr fun y : U ↦
          norm_nonneg (x - (y : E))⟩
        (⟨c, hcFixed⟩ : U)
    _ = dist x c := (dist_eq_norm x c).symm
    _ ≤ A := hxc

end KazhdanFixedSpace
end GroupApproximation
