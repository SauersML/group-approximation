import GroupApproximation.Manuscript.NonMFNotes.Full.ExactnessCStar.CoefficientSlice
import GroupApproximation.Analysis.ReducedGroupCStarMFObstruction
import GroupApproximation.Analysis.ReducedGroupCStarSpan
import GroupApproximation.Analysis.CStarTakesakiDense

/-!
# Translation forms in `B ⊗ C*_r(G)` and their coefficients

Source: `non_mf_group_notes.tex`, section `sec:Esofic`, paragraph
"Exactness" \cite{KWExact}.  The Kirchberg--Wassermann / Ozawa argument
works with *translation forms* `∑_g b_g ⊗ λ_g`, finitely supported in `g`.

* `translationForm` --- the linear map `(G →₀ B) → B ⊗ C*_r(G)`,
  `f ↦ ∑_g f(g) ⊗ λ_g`;
* `coeffFunctional` --- the coefficient functional `c ↦ ⟪δ_h, c δ₁⟫`, a
  vector functional of the defining representation;
* `sliceLeft_coeffFunctional_translationForm` --- the `h`-th coefficient slice
  of `∑_g f(g) ⊗ λ_g` is `f(h)`;
* `norm_mk_translationForm_apply_le` --- the coefficients of an approximant of
  a kernel element of `q ⊗ id` are almost in the ideal;
* `exists_translationForm_approx` --- translation forms are dense in
  `B ⊗_min C*_r(G)`.
-/

namespace GroupApproximation.Full.NN09c

open GroupApproximation.CStarTensor GroupApproximation.CStarState
open GroupApproximation.ReducedGroupCStarTrace
open scoped TensorProduct InnerProductSpace

universe u v

noncomputable section

section Form

variable (G : Type u) [Group G]

local instance decEqTranslationForm : DecidableEq G := Classical.decEq G

variable (B : Type v) [CStarAlgebra B]

/-- The translation form `f ↦ ∑_g f(g) ⊗ λ_g`. -/
def translationForm : (G →₀ B) →ₗ[ℂ] B ⊗[ℂ] ReducedGroupCStar G :=
  Finsupp.lsum ℂ fun g ↦
    (TensorProduct.mk ℂ B (ReducedGroupCStar G)).flip (reducedLeftRegular G g)

theorem translationForm_single (g : G) (b : B) :
    translationForm G B (Finsupp.single g b) = b ⊗ₜ[ℂ] reducedLeftRegular G g := by
  rw [translationForm, Finsupp.lsum_single, LinearMap.flip_apply,
    TensorProduct.mk_apply]

/-- The coefficient functional `c ↦ ⟪δ_h, c δ₁⟫` on `C*_r(G)`. -/
def coeffFunctional (h : G) : ReducedGroupCStar G →ₗ[ℂ] ℂ :=
  vecFunctional (StarRep.ofStarAlgHom (reducedGroupCStarSubalgebra G).subtype)
    (lp.single 2 (1 : G) (1 : ℂ)) (lp.single 2 h (1 : ℂ))

theorem norm_single_one (h : G) : ‖(lp.single 2 h (1 : ℂ) : GroupHilbert G)‖ = 1 := by
  rw [lp.norm_single (by norm_num), norm_one]

theorem coeffFunctional_reducedLeftRegular (g h : G) :
    coeffFunctional G h (reducedLeftRegular G g) = if g = h then 1 else 0 := by
  rw [coeffFunctional, vecFunctional_apply, lp.inner_single_left]
  change ⟪(1 : ℂ), (lp.single 2 (1 : G) (1 : ℂ)) (g⁻¹ * h)⟫_ℂ = _
  rw [lp.single_apply, RCLike.inner_apply', map_one, one_mul]
  by_cases hgh : g = h
  · rw [if_pos hgh, hgh, inv_mul_cancel, Pi.single_eq_same]
  · have hne : g⁻¹ * h ≠ 1 := fun h1 ↦ hgh (inv_mul_eq_one.mp h1)
    rw [if_neg hgh, Pi.single_eq_of_ne hne]

/-- **The coefficient slices of a translation form**: the `h`-th coefficient
slice of `∑_g f(g) ⊗ λ_g` is `f(h)`. -/
theorem sliceLeft_coeffFunctional_translationForm (h : G) (f : G →₀ B) :
    sliceLeft (coeffFunctional G h) (translationForm G B f) = f h := by
  have hlin : (sliceLeft (V := B) (coeffFunctional G h)).comp (translationForm G B)
      = Finsupp.lapply h := by
    refine Finsupp.lhom_ext fun g b ↦ ?_
    rw [LinearMap.comp_apply, translationForm_single, sliceLeft_tmul,
      coeffFunctional_reducedLeftRegular, Finsupp.lapply_apply, Finsupp.single_apply]
    by_cases hgh : g = h
    · rw [if_pos hgh, if_pos hgh, one_smul]
    · rw [if_neg hgh, if_neg hgh, zero_smul]
  exact LinearMap.congr_fun hlin f

/-- **The coefficients of an approximant of a kernel element are almost in the
ideal**: if `(q ⊗ id) z = 0`, then `‖q(f(h))‖ ≤ ‖∑_g f(g) ⊗ λ_g - z‖_min`. -/
theorem norm_mk_translationForm_apply_le [Nontrivial B] (I : Ideal B) [I.IsTwoSided]
    [IsStarStable I] [IsClosed (I : Set B)] [Nontrivial (B ⧸ I)] (f : G →₀ B) (h : G)
    {z : MinTensorProduct B (ReducedGroupCStar G)} (hz : quotientMinTensorMap I z = 0) :
    ‖Ideal.Quotient.mk I (f h)‖
      ≤ ‖minTensorIn B (ReducedGroupCStar G) (translationForm G B f) - z‖ := by
  have h1 := norm_mk_sliceLeft_le I
    (StarRep.ofStarAlgHom (reducedGroupCStarSubalgebra G).subtype)
    (lp.single 2 (1 : G) (1 : ℂ)) (lp.single 2 h (1 : ℂ)) (translationForm G B f) hz
  rw [norm_single_one, norm_single_one, one_mul, one_mul] at h1
  rw [← sliceLeft_coeffFunctional_translationForm G B h f]
  exact h1

end Form

section Density

variable (G : Type u) [Group G]
variable {B : Type v} [CStarAlgebra B] [Nontrivial B]

/-- **Translation forms are dense in `B ⊗_min C*_r(G)`.** -/
theorem exists_translationForm_approx (z : MinTensorProduct B (ReducedGroupCStar G))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : G →₀ B,
      ‖z - minTensorIn B (ReducedGroupCStar G) (translationForm G B f)‖ < ε := by
  obtain ⟨x, hx⟩ := (denseRange_minTensorIn (A := B) (B := ReducedGroupCStar G)).exists_dist_lt
    z (half_pos hε)
  obtain ⟨n, v, k, rfl⟩ := exists_fin_sum_tmul x
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∑ i, ‖v i‖ := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hM]
    exact Finset.sum_nonneg fun i _ ↦ norm_nonneg (v i)
  have hM1 : 0 < 2 * (M + 1) := mul_pos two_pos (by linarith)
  have hη : 0 < ε / (2 * (M + 1)) := div_pos hε hM1
  have happrox : ∀ i : Fin n, ∃ (m : ℕ) (c : Fin m → ℂ) (γ : Fin m → G),
      ‖((k i : ReducedGroupCStar G) : GroupHilbert G →L[ℂ] GroupHilbert G)
        - ∑ j, c j • leftRegularOperator G (γ j)‖ < ε / (2 * (M + 1)) :=
    fun i ↦ exists_translationSum_approx G (k i).2 hη
  choose m c γ hk using happrox
  let a : Fin n → ReducedGroupCStar G := fun i ↦
    ∑ j, c i j • reducedLeftRegular G (γ i j)
  have ha : ∀ i, ‖k i - a i‖ < ε / (2 * (M + 1)) := by
    intro i
    change ‖(reducedGroupCStarSubalgebra G).subtype
      (k i - ∑ j, c i j • reducedLeftRegular G (γ i j))‖ < _
    rw [map_sub, map_sum]
    simp only [map_smul]
    exact hk i
  refine ⟨∑ i, ∑ j, Finsupp.single (γ i j) (c i j • v i), ?_⟩
  have hT : translationForm G B (∑ i, ∑ j, Finsupp.single (γ i j) (c i j • v i))
      = ∑ i, v i ⊗ₜ[ℂ] a i := by
    simp only [map_sum, translationForm_single, a, TensorProduct.tmul_sum,
      TensorProduct.smul_tmul]
  have hdiff : minTensorIn B (ReducedGroupCStar G) (∑ i, v i ⊗ₜ[ℂ] k i)
      - minTensorIn B (ReducedGroupCStar G)
          (translationForm G B (∑ i, ∑ j, Finsupp.single (γ i j) (c i j • v i)))
      = ∑ i, minTensorIn B (ReducedGroupCStar G) (v i ⊗ₜ[ℂ] (k i - a i)) := by
    rw [hT, ← map_sub, ← Finset.sum_sub_distrib, map_sum]
    simp only [TensorProduct.tmul_sub]
  have hbound : ‖∑ i, minTensorIn B (ReducedGroupCStar G) (v i ⊗ₜ[ℂ] (k i - a i))‖
      ≤ M * (ε / (2 * (M + 1))) := by
    refine (norm_sum_le _ _).trans ?_
    rw [hM, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [norm_minTensorIn_tmul]
    exact mul_le_mul_of_nonneg_left (ha i).le (norm_nonneg _)
  have hsmall : M * (ε / (2 * (M + 1))) < ε / 2 := by
    rw [mul_div_assoc', div_lt_div_iff₀ hM1 (by norm_num)]
    nlinarith
  rw [dist_eq_norm] at hx
  calc ‖z - minTensorIn B (ReducedGroupCStar G)
        (translationForm G B (∑ i, ∑ j, Finsupp.single (γ i j) (c i j • v i)))‖
      ≤ ‖z - minTensorIn B (ReducedGroupCStar G) (∑ i, v i ⊗ₜ[ℂ] k i)‖
        + ‖minTensorIn B (ReducedGroupCStar G) (∑ i, v i ⊗ₜ[ℂ] k i)
          - minTensorIn B (ReducedGroupCStar G)
            (translationForm G B (∑ i, ∑ j, Finsupp.single (γ i j) (c i j • v i)))‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := by
        rw [hdiff]
        exact add_lt_add hx (hbound.trans_lt hsmall)
    _ = ε := add_halves ε

end Density

end

end GroupApproximation.Full.NN09c
