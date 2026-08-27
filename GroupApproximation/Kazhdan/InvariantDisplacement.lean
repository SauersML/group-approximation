import GroupApproximation.Kazhdan.KazhdanProjection

/-!
# Quantitative rigidity relative to the invariant subspace

Let `Q` be a Kazhdan set with constant `κ` for an orthogonal
representation `ρ`.  If a linear isometry `τ` fixes every `ρ`-invariant
vector, then the displacement of an arbitrary vector `v` by `τ` is controlled
by the displacement of `v` on `Q`:

`‖τ v - v‖ ≤ (2 / κ) * δ`

whenever `‖ρ q v - v‖ ≤ δ` for every `q ∈ Q`.

The proof is internal and dimension-free.  Orthogonally project `v` onto the
invariant subspace.  The isometry fixes the projected component, so it moves
`v` by at most twice the norm of the orthogonal component.  The defining
Kazhdan inequality bounds that component by `δ / κ`.

For the conjugation representation on a matrix Hilbert space, invariant
vectors are the exact commutant.  Taking `τ` to be conjugation by an element
which centralizes that commutant gives the projective-commutant estimate used
in the gauge obstruction, without making matrix dimension or an external
property-`(T)` theorem part of this statement.
-/

namespace GroupApproximation

open scoped InnerProductSpace

universe u v

namespace IsKazhdanPair

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- **Invariant-subspace displacement rigidity.**  Suppose `Q` has Kazhdan
constant `κ` for `G`.  An isometry fixing the invariant subspace pointwise
moves a vector by at most `2 / κ` times its largest allowed displacement on
`Q`.

This is the dimension-free Hilbert-space statement behind quantitative
projective-commutant rigidity. -/
theorem norm_displacement_le_two_div_kazhdan
    {Q : Finset G} {κ δ : ℝ} (hQ : IsKazhdanPair.{u, v} G Q κ)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (τ : E ≃ₗᵢ[ℝ] E) (v : E)
    (hτ : ∀ x ∈ KazhdanOrthogonal.invariantSubmodule ρ, τ x = x)
    (hδ : 0 ≤ δ) (hnear : ∀ q ∈ Q, ‖ρ q v - v‖ ≤ δ) :
    ‖τ v - v‖ ≤ (2 / κ) * δ := by
  let U := KazhdanOrthogonal.invariantSubmodule ρ
  letI : CompleteSpace U :=
    (KazhdanProjection.isClosed_invariantSubmodule ρ).completeSpace_coe
  let p : E := U.starProjection v
  let m : E := v - p
  have hpU : p ∈ U := U.starProjection_apply_mem v
  have hmU : m ∈ Uᗮ := U.sub_starProjection_mem_orthogonal v
  have hτp : τ p = p := hτ p hpU
  have hτm : τ v - v = τ m - m := by
    change τ v - v = τ (v - p) - (v - p)
    rw [map_sub, hτp]
    abel
  have hτm_le : ‖τ m - m‖ ≤ 2 * ‖m‖ := by
    calc
      ‖τ m - m‖ ≤ ‖τ m‖ + ‖m‖ := norm_sub_le _ _
      _ = 2 * ‖m‖ := by rw [τ.norm_map]; ring
  by_cases hm : m = 0
  · rw [hτm, hm]
    simp only [map_zero, sub_self, norm_zero]
    exact mul_nonneg (div_nonneg (by norm_num) hQ.1.le) hδ
  · obtain ⟨q, hqQ, hmove⟩ :=
      KazhdanOrthogonal.exists_moved_mul_norm_of_mem_orthogonal
        hQ ρ hmU hm
    have hpfix : ρ q p = p :=
      (KazhdanOrthogonal.mem_invariantSubmodule ρ p).mp hpU q
    have hmove_eq : ρ q m - m = ρ q v - v := by
      change ρ q (v - p) - (v - p) = ρ q v - v
      rw [map_sub, hpfix]
      abel
    have hκmδ : κ * ‖m‖ ≤ δ := by
      calc
        κ * ‖m‖ ≤ ‖ρ q m - m‖ := hmove
        _ = ‖ρ q v - v‖ := congrArg norm hmove_eq
        _ ≤ δ := hnear q hqQ
    have hm_le : ‖m‖ ≤ δ / κ := (le_div_iff₀ hQ.1).mpr (by
      simpa [mul_comm] using hκmδ)
    rw [hτm]
    calc
      ‖τ m - m‖ ≤ 2 * ‖m‖ := hτm_le
      _ ≤ 2 * (δ / κ) := mul_le_mul_of_nonneg_left hm_le (by norm_num)
      _ = (2 / κ) * δ := by ring

end IsKazhdanPair
end GroupApproximation
