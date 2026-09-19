import GroupApproximation.Kazhdan.KazhdanOrthogonal

/-!
# Laplacians of finite subsets in orthogonal representations

This file supplies the representation-theoretic first layer used by direct
sum-of-squares proofs of property (T).  For a finite subset `S` of a group and
an orthogonal representation `ρ`, `laplacian S ρ` is the evaluation of the
group-ring element

`∑ s ∈ S, (1 - s)`.

The main identities identify its quadratic form with the sum of squared
displacements and identify its kernel with the invariant subspace when `S`
generates the group.  Symmetry of `S` is needed later to view the operator as
self-adjoint; the energy and kernel statements themselves do not require it.
-/

namespace GroupApproximation
namespace GroupRingLaplacian

open scoped InnerProductSpace

universe u v

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Evaluation of the finite-set group-ring Laplacian `∑ s ∈ S, (1 - s)` in
an orthogonal representation. -/
noncomputable def laplacian (S : Finset G) (ρ : G →* (E ≃ₗᵢ[ℝ] E)) :
    E →L[ℝ] E :=
  ∑ g ∈ S, (ContinuousLinearMap.id ℝ E -
    (ρ g).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp]
theorem laplacian_apply (S : Finset G) (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    laplacian S ρ x = ∑ g ∈ S, (x - ρ g x) := by
  classical
  simp [laplacian]

/-- The elementary displacement identity for an orthogonal operator. -/
theorem two_mul_inner_sub_orbit (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (g : G) (x : E) :
    2 * inner ℝ x (x - ρ g x) = ‖ρ g x - x‖ ^ 2 := by
  rw [norm_sub_sq_real, (ρ g).norm_map]
  simp only [inner_sub_right, real_inner_self_eq_norm_sq]
  rw [real_inner_comm x (ρ g x)]
  ring

/-- The quadratic form of the evaluated Laplacian is the displacement energy.
This identity does not require inverse-closure of `S`. -/
theorem two_mul_inner_laplacian (S : Finset G) (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    2 * inner ℝ x (laplacian S ρ x) =
      ∑ g ∈ S, ‖ρ g x - x‖ ^ 2 := by
  classical
  rw [laplacian_apply, inner_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g hg
  exact two_mul_inner_sub_orbit ρ g x

/-- The evaluated Laplacian has nonnegative quadratic form. -/
theorem inner_laplacian_nonneg (S : Finset G) (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    0 ≤ inner ℝ x (laplacian S ρ x) := by
  have henergy := two_mul_inner_laplacian S ρ x
  have hnonneg : 0 ≤ ∑ g ∈ S, ‖ρ g x - x‖ ^ 2 := by
    exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  linarith

/-- A vector lies in the kernel of the finite-set Laplacian exactly when every
element of the finite set fixes it. -/
theorem laplacian_apply_eq_zero_iff (S : Finset G) (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    laplacian S ρ x = 0 ↔ ∀ g ∈ S, ρ g x = x := by
  classical
  constructor
  · intro hx g hg
    have hsum : ∑ g ∈ S, ‖ρ g x - x‖ ^ 2 = 0 := by
      rw [← two_mul_inner_laplacian S ρ x, hx]
      simp
    have hterm : ‖ρ g x - x‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _).mp hsum g hg
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hterm))
  · intro hfix
    rw [laplacian_apply]
    apply Finset.sum_eq_zero
    intro g hg
    rw [hfix g hg, sub_self]

/-- If `S` generates `G`, the kernel of its Laplacian is precisely the space
of invariant vectors. -/
theorem laplacian_apply_eq_zero_iff_invariant
    (S : Finset G) (hgen : Subgroup.closure (S : Set G) = ⊤)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    laplacian S ρ x = 0 ↔ x ∈ KazhdanOrthogonal.invariantSubmodule ρ := by
  rw [laplacian_apply_eq_zero_iff]
  constructor
  · intro hfix
    rw [KazhdanOrthogonal.mem_invariantSubmodule]
    let stabilizer : Subgroup G :=
      { carrier := {g | ρ g x = x}
        one_mem' := by simp
        mul_mem' := by
          intro a b ha hb
          change ρ a x = x at ha
          change ρ b x = x at hb
          change ρ (a * b) x = x
          rw [map_mul]
          change ρ a (ρ b x) = x
          rw [hb, ha]
        inv_mem' := by
          intro g hg
          have h := congrArg (fun y : E ↦ ρ g⁻¹ y) hg
          simpa using h.symm }
    have hS : (S : Set G) ⊆ stabilizer := by
      intro g hg
      exact hfix g hg
    have htop : stabilizer = ⊤ := by
      apply top_unique
      rw [← hgen]
      exact (Subgroup.closure_le stabilizer).2 hS
    intro g
    have hg : g ∈ stabilizer := by rw [htop]; exact Subgroup.mem_top g
    exact hg
  · intro hinv g hg
    exact (KazhdanOrthogonal.mem_invariantSubmodule ρ x).mp hinv g

/-- Submodule form of `laplacian_apply_eq_zero_iff_invariant`. -/
theorem ker_laplacian_eq_invariant
    (S : Finset G) (hgen : Subgroup.closure (S : Set G) = ⊤)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) :
    LinearMap.ker (laplacian S ρ).toLinearMap =
      KazhdanOrthogonal.invariantSubmodule ρ := by
  ext x
  exact laplacian_apply_eq_zero_iff_invariant S hgen ρ x

end GroupRingLaplacian
end GroupApproximation
