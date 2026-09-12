import GroupApproximation.KunThom.FixedPointNormalizationPatching
import Mathlib.Data.Nat.Cast.Order.Field

/-!
# Summing per-block quantities over disjoint blocks

Kun--Thom's estimates (arXiv:2608.06222v3, proof of Theorem 4.1) bound
per-block errors by a vanishing multiple of the block size: the improvement
distance `d_n * |C|` and the candidate threshold `h_n * scale C / 2` at scale
`|C| / 18`.  Over pairwise disjoint blocks inside one model the block sizes
sum to at most the model size.  These lemmas turn such per-block bounds into
negligible totals.
-/

namespace GroupApproximation
namespace BlockPatching
namespace BlockEmbedding

universe u

variable {Y : FiniteModel} {I : Type u} [Fintype I]

/-- Pairwise disjoint blocks carry at most `|Y|` points in total. -/
theorem sum_card_model_le (E : BlockEmbedding Y I) :
    ∑ C, Fintype.card (E.model C) ≤ Fintype.card Y := by
  classical
  have hinj : Function.Injective (fun p : Σ C, E.model C ↦ E.embed p.1 p.2) := by
    rintro ⟨C, x⟩ ⟨C', z⟩ h
    have hCC : C = C' := E.embed_disjoint C C' x z h
    subst hCC
    have hxz : x = z := E.embed_injective C h
    subst hxz
    rfl
  have hcard := Fintype.card_le_of_injective _ hinj
  simpa only [Fintype.card_sigma] using hcard

/-- A per-block bound `d * |C|` sums to at most `d * |Y|`. -/
theorem sum_mul_card_model_le (E : BlockEmbedding Y I) {d : ℝ} (hd : 0 ≤ d) :
    ∑ C, d * (Fintype.card (E.model C) : ℝ) ≤ d * Fintype.card Y := by
  have hsum : ((∑ C, Fintype.card (E.model C) : ℕ) : ℝ) ≤ Fintype.card Y := by
    exact_mod_cast E.sum_card_model_le
  rw [← Finset.mul_sum, ← Nat.cast_sum]
  exact mul_le_mul_of_nonneg_left hsum hd

/-- **The candidate threshold at scale `|C| / 18`.**  The per-block threshold
`h * (|C| / 18) / 2` sums to at most `h / 36` times the model size. -/
theorem sum_scaleThreshold_le (E : BlockEmbedding Y I) {h : ℝ} (hh : 0 ≤ h) :
    ∑ C, h * ((Fintype.card (E.model C) / 18 : ℕ) : ℝ) / 2 ≤
      h / 36 * Fintype.card Y := by
  have hblock : ∀ C, h * ((Fintype.card (E.model C) / 18 : ℕ) : ℝ) / 2 ≤
      h / 36 * (Fintype.card (E.model C) : ℝ) := fun C ↦ by
    have hcast : ((Fintype.card (E.model C) / 18 : ℕ) : ℝ) ≤
        (Fintype.card (E.model C) : ℝ) / 18 := Nat.cast_div_le
    have hmul := mul_le_mul_of_nonneg_left hcast hh
    have heq : h * ((Fintype.card (E.model C) : ℝ) / 18) / 2 =
        h / 36 * (Fintype.card (E.model C) : ℝ) := by ring
    linarith
  calc ∑ C, h * ((Fintype.card (E.model C) / 18 : ℕ) : ℝ) / 2
      ≤ ∑ C, h / 36 * (Fintype.card (E.model C) : ℝ) :=
        Finset.sum_le_sum fun C _ ↦ hblock C
    _ ≤ h / 36 * Fintype.card Y :=
        E.sum_mul_card_model_le (div_nonneg hh (by norm_num))

end BlockEmbedding
end BlockPatching
end GroupApproximation
