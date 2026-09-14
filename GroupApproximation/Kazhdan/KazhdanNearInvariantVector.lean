import GroupApproximation.Kazhdan.KazhdanFixedSpace

/-!
# Almost invariant vectors are near invariant vectors

For a Kazhdan pair `(Q, ε)` and an orthogonal representation on a complete
real Hilbert space, a vector moved by less than `ε δ` by every element of `Q`
lies within `δ` of an invariant vector, namely its orthogonal projection onto
the invariant vectors.

The proof applies the Kazhdan pair to the representation on the orthogonal
complement of the invariant vectors, which has no invariant vectors
(`KazhdanFixedSpace.movingRepresentation_hasNoInvariantVectors`).  The component
of the vector there is moved exactly as the vector is, so it is short.

This is the step of Kirchberg's Theorem 1.1 that turns the almost invariant
vector of the tensor square, built from the matrix models of an amenable trace,
into an invariant one.
-/

namespace GroupApproximation
namespace KazhdanNearInvariantVector

open KazhdanFixedSpace

universe u v

variable {G : Type u} [Group G] {Q : Finset G} {ε : ℝ}

/-- **Almost invariant vectors are near invariant vectors.**  If every element
of the Kazhdan set moves `η` by less than `ε δ`, then `η` lies within `δ` of an
invariant vector. -/
theorem exists_invariant_near (hQ : IsKazhdanPair.{u, v} G Q ε)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (η : E) {δ : ℝ} (hδ : 0 < δ)
    (hmove : ∀ q ∈ Q, ‖ρ q η - η‖ < ε * δ) :
    ∃ ζ : E, (∀ g : G, ρ g ζ = ζ) ∧ ‖η - ζ‖ < δ := by
  haveI : CompleteSpace (fixedSubspace ρ ⊤) :=
    (isClosed_fixedSubspace ρ ⊤).completeSpace_coe
  let ζ : E := (fixedSubspace ρ ⊤).starProjection η
  have hζfix : ∀ g : G, ρ g ζ = ζ := fun g ↦
    (mem_fixedSubspace_iff ρ ⊤ ζ).1
      (Submodule.starProjection_apply_mem (fixedSubspace ρ ⊤) η) g (Subgroup.mem_top g)
  refine ⟨ζ, hζfix, ?_⟩
  by_cases hξ : η - ζ = 0
  · rw [hξ, norm_zero]
    exact hδ
  have hmemo : η - ζ ∈ movingSubspace ρ := by
    show η - ζ ∈ (fixedSubspace ρ ⊤)ᗮ
    exact Submodule.sub_starProjection_mem_orthogonal η
  haveI : CompleteSpace (movingSubspace ρ) :=
    (Submodule.isClosed_orthogonal (fixedSubspace ρ ⊤)).completeSpace_coe
  let x : movingSubspace ρ := ⟨η - ζ, hmemo⟩
  have hx0 : x ≠ 0 := fun h ↦ hξ (congrArg Subtype.val h)
  obtain ⟨q, hq, hmoved⟩ := IsKazhdanPair.exists_moved_mul_norm_of_noInvariant hQ
    (movingRepresentation ρ) (movingRepresentation_hasNoInvariantVectors ρ) x hx0
  have hcoe : ((movingRepresentation ρ q x - x : movingSubspace ρ) : E) = ρ q η - η := by
    change ρ q (η - ζ) - (η - ζ) = ρ q η - η
    rw [map_sub, hζfix q]
    abel
  have hnorm : ‖movingRepresentation ρ q x - x‖ = ‖ρ q η - η‖ := by
    rw [← hcoe]
    rfl
  have hlt : ε * ‖η - ζ‖ < ε * δ :=
    calc ε * ‖η - ζ‖ = ε * ‖x‖ := rfl
      _ ≤ ‖movingRepresentation ρ q x - x‖ := hmoved
      _ = ‖ρ q η - η‖ := hnorm
      _ < ε * δ := hmove q hq
  exact lt_of_mul_lt_mul_left hlt hQ.1.le

end KazhdanNearInvariantVector
end GroupApproximation
