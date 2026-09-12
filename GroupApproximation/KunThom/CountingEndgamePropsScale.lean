import GroupApproximation.KunThom.CountingEndgameProps
import GroupApproximation.KunThom.RelativeFunctorScaled
import GroupApproximation.KunThom.CompressorNormalizationAssemblyThreshold

/-!
# Sizes and scales for the counting Props

Two quantitative inputs of the counting in Kun and Thom's proof of Theorem 4.1
(arXiv:2608.06222v3, §4).

* Equation (1): an allowed arrow changes the component size by a bounded factor.
  In a scaled cluster system every representative joins objects whose scales agree
  up to `11 / 10`, and the scale is a fixed fraction of the size, so the size at most
  doubles along every arrow (`card_model_le_two_mul_of_rep`,
  `card_model_le_two_mul_of_hom`).  `half_card_model_le_of_mem_orbit` states this
  in the form consumed by `CountingEndgame.mul_sum_le_of_dirty`.
* The slow cleanliness scale (tex lines 1152–1156): for a nonnegative vanishing
  density `e`, `cleanScale e n = min (√(e n) + 1 / (n + 1)) (1 / 2)` is positive, at
  most `1 / 2`, vanishes (`vanishing_cleanScale`), and `e / cleanScale e` vanishes
  (`vanishing_div_cleanScale`).
-/

namespace GroupApproximation
namespace CountingEndgame

open CategoryTheory GroupoidPresentation

universe u

/-- A representative of a scaled cluster presentation from `X` to `Y` forces
`|X| ≤ 2 |Y|`. -/
theorem card_model_le_two_mul_of_rep {I : Type u} [Fintype I] {L : Type*} [Fintype L]
    [DecidableEq L] [Nonempty L] (D : ScaledPartialClusterSystem I L) {X Y : I}
    (f : D.clusterData.Rep X Y) :
    Fintype.card (D.model X) ≤ 2 * Fintype.card (D.model Y) := by
  obtain ⟨h₁, -⟩ := D.scale_comparable_of_rep f
  have hX := D.scale_eq X
  have hY := D.scale_eq Y
  have hlarge := D.scale_large Y
  omega

/-- An arrow of a scaled cluster groupoid from `X` to `Y` forces `|X| ≤ 2 |Y|`. -/
theorem card_model_le_two_mul_of_hom {I : Type u} [Fintype I] {L : Type*} [Fintype L]
    [DecidableEq L] [Nonempty L] (D : ScaledPartialClusterSystem I L)
    {X Y : D.presentation.Obj} (f : X ⟶ Y) :
    Fintype.card (D.model X.val) ≤ 2 * Fintype.card (D.model Y.val) :=
  card_model_le_two_mul_of_rep D (Quotient.out (f : Quotient (D.presentation.rel X.val Y.val)))

/-- Sizes inside an orbit of a scaled cluster groupoid vary by at most the factor
`1 - 1 / 2`. -/
theorem half_card_model_le_of_mem_orbit {I : Type u} [Fintype I] {L : Type*} [Fintype L]
    [DecidableEq L] [Nonempty L] (D : ScaledPartialClusterSystem I L)
    (X : D.presentation.Obj) :
    ∀ Y ∈ FiniteGroupoid.orbit X,
      (1 - 1 / 2 : ℝ) * Fintype.card (D.model X.val) ≤ Fintype.card (D.model Y.val) := by
  intro Y hY
  obtain ⟨f⟩ := (FiniteGroupoid.mem_orbit X Y).mp hY
  have hcast : (Fintype.card (D.model X.val) : ℝ) ≤ 2 * Fintype.card (D.model Y.val) := by
    exact_mod_cast card_model_le_two_mul_of_hom D f
  linarith

/-- The cleanliness scale of a density `e`. -/
noncomputable def cleanScale (e : ℕ → ℝ) (n : ℕ) : ℝ :=
  min (Real.sqrt (e n) + 1 / ((n : ℝ) + 1)) (1 / 2)

theorem cleanScale_pos (e : ℕ → ℝ) (n : ℕ) : 0 < cleanScale e n := by
  have h₁ : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have h₂ := Real.sqrt_nonneg (e n)
  unfold cleanScale
  exact lt_min (by linarith) (by norm_num)

theorem cleanScale_le_half (e : ℕ → ℝ) (n : ℕ) : cleanScale e n ≤ 1 / 2 := by
  unfold cleanScale
  exact min_le_right _ _

/-- `1 / (n + 1)` vanishes. -/
theorem vanishing_one_div_succ : Vanishing fun n : ℕ ↦ 1 / ((n : ℝ) + 1) := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, fun n hn ↦ ?_⟩
  show |1 / ((n : ℝ) + 1)| < ε
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have h₁ : 1 / ε < (n : ℝ) + 1 := by linarith
  have h₂ : 1 < ((n : ℝ) + 1) * ε := (div_lt_iff₀ hε).mp h₁
  rw [abs_of_pos (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity), div_lt_iff₀ hpos]
  linarith

/-- The cleanliness scale of a nonnegative vanishing density vanishes. -/
theorem vanishing_cleanScale {e : ℕ → ℝ} (he0 : ∀ n, 0 ≤ e n) (he : Vanishing e) :
    Vanishing (cleanScale e) := by
  refine Vanishing.squeeze (fun n ↦ (cleanScale_pos e n).le) (fun n ↦ ?_)
    ((CompressorNormalizationAssembly.vanishing_sqrt he0 he).add vanishing_one_div_succ)
  show cleanScale e n ≤ Real.sqrt (e n) + 1 / ((n : ℝ) + 1)
  unfold cleanScale
  exact min_le_left _ _

/-- A nonnegative vanishing density is negligible against its cleanliness scale. -/
theorem vanishing_div_cleanScale {e : ℕ → ℝ} (he0 : ∀ n, 0 ≤ e n) (he : Vanishing e) :
    Vanishing fun n ↦ e n / cleanScale e n := by
  obtain ⟨N, hN⟩ := CompressorNormalizationAssembly.vanishing_sqrt he0 he (1 / 2)
    (by norm_num)
  refine CompressorNormalizationAssembly.vanishing_div_of_sqrt_le he0 he (cleanScale_pos e) N
    fun n hn ↦ ?_
  have h₁ : |Real.sqrt (e n)| < 1 / 2 := hN n hn
  rw [abs_of_nonneg (Real.sqrt_nonneg _)] at h₁
  have h₂ : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
  unfold cleanScale
  exact le_min (by linarith) h₁.le

end CountingEndgame
end GroupApproximation
