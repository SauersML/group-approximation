import GroupApproximation.Kazhdan.KazhdanProjection

/-!
# The Kazhdan eigenvalue bound

Any eigenvalue of the orbit average of a Kazhdan set, other than `1`, is
at most the machine rate `1 - ε²/(4|S|)`.  The proof projects the
eigenvalue equation onto the invariant subspace — the average fixes the
invariant part and preserves its complement, so a `μ ≠ 1` eigenvector has
no invariant component — and then applies the one-step contraction of
`norm_averageOperator_pow_le` on the complement.  No limits are needed.

This is the spectral-gap payoff brick of the strict-Kazhdan-compression
program of `notes/FORMALIZATION_DIRECTIVES_2026-08-15.md` §1: combined
with the GNS eigenvector of a spectrally concentrated state it forbids
abstract C-star spectrum of the averaging element in the gap window.
-/

namespace GroupApproximation
namespace KazhdanEigenvalueBound

open KazhdanProjection
open scoped InnerProductSpace

universe u v

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Kazhdan eigenvalue bound**: an eigenvalue of the orbit average on a
nonzero eigenvector is either `1` or at most `1 - ε²/(4|S|)`. -/
theorem eigenvalue_le_of_ne_one [CompleteSpace E]
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, v} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {x : E} (hx : x ≠ 0) {μ : ℝ} (hμ1 : μ ≠ 1)
    (heig : averageOperator S ρ x = μ • x) :
    μ ≤ 1 - ε ^ 2 / (4 * S.card) := by
  classical
  set U := KazhdanOrthogonal.invariantSubmodule ρ with hU
  letI : CompleteSpace U := (isClosed_invariantSubmodule ρ).completeSpace_coe
  set p : E := U.starProjection x with hp
  set w : E := Uᗮ.starProjection x with hw
  have hpmem : p ∈ U := U.starProjection_apply_mem x
  have hwmem : w ∈ Uᗮ := Uᗮ.starProjection_apply_mem x
  have hsplit : p + w = x :=
    U.starProjection_add_starProjection_orthogonal x
  have hTp : averageOperator S ρ p = p :=
    averageOperator_apply_of_invariant S hone ρ hpmem
  have hTw : averageOperator S ρ w ∈ Uᗮ :=
    averageOperator_mem_orthogonal S ρ hwmem
  have hproj : U.starProjection (averageOperator S ρ x) = p := by
    have hTx : averageOperator S ρ x = p + averageOperator S ρ w := by
      conv_lhs => rw [← hsplit]
      rw [map_add, hTp]
    rw [hTx, map_add]
    have h1 : U.starProjection p = p :=
      Submodule.starProjection_eq_self_iff.mpr hpmem
    have h2 : U.starProjection (averageOperator S ρ w) = 0 := by
      apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
        (Submodule.zero_mem U)
      intro z hz
      rw [sub_zero]
      exact (Submodule.mem_orthogonal' U _).mp hTw z hz
    rw [h1, h2, add_zero]
  have h3 := hproj
  rw [heig, map_smul, ← hp] at h3
  have h4 : (1 - μ) • p = 0 := by
    rw [sub_smul, one_smul, h3, sub_self]
  have h5 : (1 - μ) ≠ 0 := sub_ne_zero_of_ne (Ne.symm hμ1)
  have hp0 : p = 0 := (smul_eq_zero.mp h4).resolve_left h5
  have hxmem : x ∈ Uᗮ := by
    rw [← hsplit, hp0, zero_add]
    exact hwmem
  have hbound := norm_averageOperator_pow_le hQ S hQS hone hεone ρ hxmem 1
  rw [pow_one, pow_one, heig, norm_smul, Real.norm_eq_abs] at hbound
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have habs : |μ| ≤ 1 - ε ^ 2 / (4 * S.card) :=
    le_of_mul_le_mul_right hbound hxpos
  exact (le_abs_self μ).trans habs

end KazhdanEigenvalueBound
end GroupApproximation
