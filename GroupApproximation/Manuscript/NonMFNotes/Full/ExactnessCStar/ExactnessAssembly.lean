import GroupApproximation.Manuscript.NonMFNotes.Full.ExactnessCStar.ExactnessEstimates

/-!
# Property A implies exactness of the reduced group C⋆-algebra

Source: `non_mf_group_notes.tex`, section `sec:Esofic`, paragraph
"Exactness", last sentence: for a discrete group, exactness of the group
gives exactness of `C*_r(G)` \cite{KWExact}.  This file assembles the
Kirchberg--Wassermann / Ozawa argument from the tensor estimates.

Let `z ∈ B ⊗_min C*_r(G)` with `(q ⊗ id) z = 0`, and `ε > 0`.

1. Approximate `z` within `ε / 8` by a translation form `x₁ = ∑_g f₁(g) ⊗ λ_g`
   with finite support `R = supp f₁`.
2. Take a property-A witness at scale `R` and tolerance
   `τ = ε / (4 (∑ ‖f₁ g‖ + 1))`, with Schur multiplier `Φ` and finite
   difference set `D`.
3. Approximate `z` within `δ = ε / (8 (3 |D| + 3))` by a translation form
   `x₂ = ∑_g f₂(g) ⊗ λ_g`.  Its coefficients are `δ`-close to `I`: write
   `f₂(g) = r_g + j_g` with `‖r_g‖ < 2δ` and `j_g ∈ I`.
4. An approximate unit `e ∈ I` with `‖1 - e‖ ≤ 1` absorbs the finitely many
   `j_g`, `g ∈ D`, up to `δ`; then `x₂ (e ⊗ 1) ∈ I ⊙ C*_r(G)`.
5. `‖z - x₂ (e ⊗ 1)‖ ≤ ‖z - x₂‖ + ‖x₂ ((1 - e) ⊗ 1)‖`, and the second term
   is at most `‖(id ⊗ (J - Φ)) x₂‖ + ‖(id ⊗ Φ)(x₂ ((1 - e) ⊗ 1))‖
   ≤ (ε / 8 + 2 (ε / 8 + δ)) + 3 |D| δ`.

* `exists_idealTensorSpan_near` --- the approximation step;
* `isExactCStar_reducedGroupCStar_of_hasPropertyA` --- **property A implies
  `IsExactCStar (C*_r(G))`**.
-/

namespace GroupApproximation.Full.NN09c

open GroupApproximation.CStarTensor GroupApproximation.ExactnessPermanence
open GroupApproximation.ReducedGroupCStarTrace
open scoped TensorProduct

universe u v

noncomputable section

section Assembly

variable {G : Type u} [Group G]

/-- **Kernel elements of `q ⊗ id` are approximated by `I ⊙ C*_r(G)`** when `G`
has property A. -/
theorem exists_idealTensorSpan_near (hA : HasPropertyA G) {B : Type v} [CStarAlgebra B]
    [Nontrivial B] (I : Ideal B) [I.IsTwoSided] [IsStarStable I] [IsClosed (I : Set B)]
    [Nontrivial (B ⧸ I)] {z : MinTensorProduct B (ReducedGroupCStar G)}
    (hz : quotientMinTensorMap I z = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ w ∈ idealTensorSpan (C := ReducedGroupCStar G) I, ‖z - w‖ < ε := by
  -- Step 1: a first approximant and the scale `R = supp f₁`.
  obtain ⟨f₁, hf₁⟩ := exists_translationForm_approx G z (div_pos hε (by norm_num : (0 : ℝ) < 8))
  obtain ⟨S₁, hS₁⟩ : ∃ S : ℝ, S = ∑ g ∈ f₁.support, ‖f₁ g‖ := ⟨_, rfl⟩
  have hS₁0 : 0 ≤ S₁ := by
    rw [hS₁]
    exact Finset.sum_nonneg fun g _ ↦ norm_nonneg (f₁ g)
  have hS₁pos : 0 < 4 * (S₁ + 1) := by linarith [hS₁0]
  obtain ⟨τ, hτ_def⟩ : ∃ τ : ℝ, τ = ε / (4 * (S₁ + 1)) := ⟨_, rfl⟩
  have hτ : 0 < τ := by
    rw [hτ_def]
    exact div_pos hε hS₁pos
  have hτeq : τ * (4 * (S₁ + 1)) = ε := by
    rw [hτ_def]
    exact div_mul_cancel₀ ε hS₁pos.ne'
  -- Step 2: the property-A witness.
  obtain ⟨W⟩ := hA f₁.support τ hτ
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ((diffSet W).card : ℝ) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact Nat.cast_nonneg _
  have hδpos : 0 < 8 * (3 * c + 3) := by linarith [hc0]
  obtain ⟨δ, hδ_def⟩ : ∃ δ : ℝ, δ = ε / (8 * (3 * c + 3)) := ⟨_, rfl⟩
  have hδ : 0 < δ := by
    rw [hδ_def]
    exact div_pos hε hδpos
  have hδeq : δ * (8 * (3 * c + 3)) = ε := by
    rw [hδ_def]
    exact div_mul_cancel₀ ε hδpos.ne'
  -- Step 3: a second approximant, with coefficients close to the ideal.
  obtain ⟨f₂, hf₂⟩ := exists_translationForm_approx G z hδ
  have hcoef : ∀ g : G, ∃ r : B, f₂ g - r ∈ I ∧ ‖r‖ < 2 * δ := by
    intro g
    have hmk : ‖Ideal.Quotient.mk I (f₂ g)‖ < δ := by
      refine (norm_mk_translationForm_apply_le G B I f₂ g hz).trans_lt ?_
      rw [norm_sub_rev]
      exact hf₂
    obtain ⟨r, hr, hrn⟩ := quotient_norm_mk_lt I (Ideal.Quotient.mk I (f₂ g)) hδ
    refine ⟨r, Ideal.Quotient.eq.mp hr.symm, ?_⟩
    rw [two_mul]
    exact hrn.trans_le (add_le_add hmk.le le_rfl)
  choose r hrI hrn using hcoef
  -- Step 4: an approximate unit absorbing the ideal parts on the difference set.
  obtain ⟨e, heI, he1, heabs⟩ :=
    exists_approxUnit_absorb I (diffSet W) (fun g ↦ f₂ g - r g) (fun g _ ↦ hrI g) hδ
  have hterm : ∀ g ∈ diffSet W, ‖f₂ g * (1 - e)‖ ≤ 3 * δ := by
    intro g hg
    have hid : f₂ g * (1 - e) = r g * (1 - e) + ((f₂ g - r g) - (f₂ g - r g) * e) := by
      simp only [mul_sub, sub_mul, mul_one]
      abel
    have h1 : ‖r g * (1 - e)‖ ≤ 2 * δ :=
      (norm_mul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) he1).trans (hrn g).le)
    have h2 : ‖(f₂ g - r g) - (f₂ g - r g) * e‖ < δ := heabs g hg
    rw [hid]
    refine (norm_add_le _ _).trans ?_
    linarith [h1, h2]
  -- Step 5: the element of `I ⊙ C*_r(G)` and the estimate.
  refine ⟨minTensorIn B (ReducedGroupCStar G)
      (translationForm G B f₂ * (e ⊗ₜ[ℂ] (1 : ReducedGroupCStar G))),
    minTensorIn_mul_tmul_one_mem I _ heI, ?_⟩
  have hsplit : z - minTensorIn B (ReducedGroupCStar G)
        (translationForm G B f₂ * (e ⊗ₜ[ℂ] (1 : ReducedGroupCStar G)))
      = (z - minTensorIn B (ReducedGroupCStar G) (translationForm G B f₂))
        + minTensorIn B (ReducedGroupCStar G)
          (translationForm G B f₂ * ((1 - e) ⊗ₜ[ℂ] (1 : ReducedGroupCStar G))) := by
    rw [TensorProduct.sub_tmul, mul_sub, ← Algebra.TensorProduct.one_def, mul_one,
      map_sub (minTensorIn B (ReducedGroupCStar G))]
    abel
  have hΦ := norm_lTensor_schurMultiplier_mul_le W f₂ e hterm
  rw [← hc] at hΦ
  have hΔ := norm_lTensor_schurDefect_le_of_near W f₁ f₂ (Finset.Subset.refl _) z
  have hE := norm_lTensor_regInclusion_mul_le W (translationForm G B f₂) he1
  have hS : (∑ g ∈ f₁.support, ‖f₁ g‖) * (τ / 2) ≤ ε / 8 := by
    rw [← hS₁]
    linarith [hτeq, hτ]
  rw [hsplit]
  calc _ ≤ ‖z - minTensorIn B (ReducedGroupCStar G) (translationForm G B f₂)‖
        + ‖minTensorIn B (ReducedGroupCStar G)
          (translationForm G B f₂ * ((1 - e) ⊗ₜ[ℂ] (1 : ReducedGroupCStar G)))‖ :=
        norm_add_le _ _
    _ < ε := by linarith [hf₁, hf₂, hE, hΔ, hΦ, hS, hδeq, hc0, hδ, hε]

/-- **Property A implies exactness of the reduced group C⋆-algebra**
(Kirchberg--Wassermann, Ozawa).  `non_mf_group_notes.tex`, section
`sec:Esofic`, paragraph "Exactness" \cite{KWExact}. -/
theorem isExactCStar_reducedGroupCStar_of_hasPropertyA (hA : HasPropertyA G) :
    IsExactCStar.{v} (ReducedGroupCStar G) := by
  intro B _ _ I _ _ _ _ z hz
  exact Metric.mem_closure_iff.mpr fun ε hε ↦ by
    obtain ⟨w, hw, hzw⟩ := exists_idealTensorSpan_near hA I hz hε
    exact ⟨w, hw, by rw [dist_eq_norm]; exact hzw⟩

end Assembly

end

end GroupApproximation.Full.NN09c
