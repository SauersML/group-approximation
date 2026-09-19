import GroupApproximation.Sofic.HilbertUltraproductPairing

/-!
# `⟨[ξ], [η]⟩ = lim_ω Tr(ξ_n* η_n)/w_n`

The inner product the printed proof of `thm:kazhdan-transport` uses on `K_ω`,
built on the numerator of `Sofic/UltraproductModelConstruction.lean`'s `Vec`.
Everything here is a statement about mass-bounded families; the descent to the
quotient is immediate from `uinner_eq_zero_of_massNull_left` below, which is the
only step that needs an idea rather than a computation.

Conventions follow Mathlib: the form is **conjugate-linear in the first
argument** and linear in the second, so the coordinate form is `Tr(ξ_n* η_n)`
and `uinner ξ ξ` is the renormalized mass.
-/

namespace GroupApproximation
namespace HilbertUltraproductInner

open Filter Matrix Topology
open FrobeniusPairing UltrafilterLimit UltraproductModelConstruction
open HilbertUltraproductPairing ScaledKazhdanTransport

noncomputable section

variable {Y : ℕ → FiniteModel} {w : ℕ → ℝ} {ω : Ultrafilter ℕ}

/-- The real coercion commutes with `lim_ω`; used to read the self-pairing as a
real number. -/
theorem ulim_ofReal {f : ℕ → ℝ} (hf : ∃ L : ℝ, Tendsto f (ω : Filter ℕ) (𝓝 L)) :
    ulim ω (fun n ↦ ((f n : ℝ) : ℂ)) = ((ulim ω f : ℝ) : ℂ) :=
  ulim_eq ((Complex.continuous_ofReal.tendsto _).comp (tendsto_ulim hf))

/-- Every mass-bounded pair of families has a coordinate pairing that converges
along `ω`. -/
theorem exists_tendsto_pairAt (hw : ∀ n, 0 ≤ w n)
    (ξ η : massBounded Y w) :
    ∃ L : ℂ, Tendsto (pairAt Y w (ξ : MatFam Y) (η : MatFam Y))
      (ω : Filter ℕ) (𝓝 L) := by
  obtain ⟨Cx, hx⟩ := ξ.2
  obtain ⟨Cy, hy⟩ := η.2
  exact exists_tendsto_of_bounded ω (norm_pairAt_le hw hx hy)

/-- The renormalized mass of a mass-bounded family converges along `ω`. -/
theorem exists_tendsto_mass (hw : ∀ n, 0 ≤ w n) (ξ : massBounded Y w) :
    ∃ L : ℝ, Tendsto (fun n ↦ matMass ((ξ : MatFam Y) n) / w n)
      (ω : Filter ℕ) (𝓝 L) := by
  obtain ⟨Cx, hx⟩ := ξ.2
  refine exists_tendsto_of_bounded ω (C := max Cx 0) fun n ↦ ?_
  rcases (hw n).lt_or_eq with hpos | hzero
  · rw [Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (matMass_nonneg _) (hw n)), div_le_iff₀ hpos]
    nlinarith [hx n, le_max_left Cx 0, hpos.le]
  · have hxn : (ξ : MatFam Y) n = 0 := eq_zero_of_weight_eq_zero hx hzero.symm
    rw [hxn]
    simp [matMass_zero, le_max_right Cx 0]

/-- **The inner product of `K_ω`**, on the numerator. -/
def uinner (ξ η : massBounded Y w) : ℂ :=
  ulim ω (pairAt Y w (ξ : MatFam Y) (η : MatFam Y))

/-- The self-pairing is the limit of the renormalized masses, hence real. -/
theorem uinner_self (hw : ∀ n, 0 ≤ w n) (ξ : massBounded Y w) :
    uinner (ω := ω) ξ ξ
      = ((ulim ω (fun n ↦ matMass ((ξ : MatFam Y) n) / w n) : ℝ) : ℂ) := by
  rw [uinner, ← ulim_ofReal (exists_tendsto_mass hw ξ)]
  exact ulim_congr (Eventually.of_forall fun n ↦ pairAt_self _ n)
    (exists_tendsto_pairAt hw ξ ξ)

/-- Positivity. -/
theorem uinner_self_nonneg (hw : ∀ n, 0 ≤ w n) (ξ : massBounded Y w) :
    0 ≤ (uinner (ω := ω) ξ ξ).re := by
  rw [uinner_self hw ξ, Complex.ofReal_re]
  refine ulim_nonneg (exists_tendsto_mass hw ξ) fun n ↦ ?_
  exact div_nonneg (matMass_nonneg _) (hw n)

/-- Conjugate symmetry. -/
theorem uinner_conj_symm (hw : ∀ n, 0 ≤ w n) (ξ η : massBounded Y w) :
    (starRingEnd ℂ) (uinner (ω := ω) η ξ) = uinner (ω := ω) ξ η := by
  have hcong : ∀ n,
      (starRingEnd ℂ) (pairAt Y w (η : MatFam Y) (ξ : MatFam Y) n)
        = pairAt Y w (ξ : MatFam Y) (η : MatFam Y) n :=
    fun n ↦ pairAt_conj _ _ n
  rw [uinner, uinner, ← ulim_conj (exists_tendsto_pairAt hw η ξ)]
  refine ulim_congr (Eventually.of_forall hcong) ?_
  exact ⟨_, (tendsto_ulim (exists_tendsto_pairAt hw ξ η)).congr
    fun n ↦ (hcong n).symm⟩

/-- Additivity in the second argument. -/
theorem uinner_add_right (hw : ∀ n, 0 ≤ w n) (ξ η ζ : massBounded Y w) :
    uinner (ω := ω) ξ (η + ζ) = uinner (ω := ω) ξ η + uinner (ω := ω) ξ ζ := by
  rw [uinner, uinner, uinner, ← ulim_add (exists_tendsto_pairAt hw ξ η)
    (exists_tendsto_pairAt hw ξ ζ)]
  refine ulim_congr (Eventually.of_forall fun n ↦ ?_)
    (exists_tendsto_pairAt hw ξ (η + ζ))
  exact pairAt_add_right _ _ _ n

/-- Homogeneity in the second argument. -/
theorem uinner_smul_right (hw : ∀ n, 0 ≤ w n) (c : ℂ) (ξ η : massBounded Y w) :
    uinner (ω := ω) ξ (c • η) = c * uinner (ω := ω) ξ η := by
  rw [uinner, uinner, ← ulim_const_mul c (exists_tendsto_pairAt hw ξ η)]
  refine ulim_congr (Eventually.of_forall fun n ↦ ?_)
    (exists_tendsto_pairAt hw ξ (c • η))
  exact pairAt_smul_right _ _ _ n

/-! ## The null step

This is the only step of the descent that is not a computation.  A family null
at the weight pairs to zero against every mass-bounded family, and the proof is
the rescaled arithmetic-geometric bound: for every `t > 0` the pairing is at
most `t · (mass ζ / w) / 2 + (mass η / w) / (2t)`, the first term vanishing
along `ω` and the second being at most `C / (2t)`. -/

theorem uinner_eq_zero_of_massNull_left (hw : ∀ n, 0 ≤ w n)
    {ζ η : massBounded Y w}
    (hζ : (ζ : MatFam Y) ∈ massNull Y w ω) :
    uinner (ω := ω) ζ η = 0 := by
  obtain ⟨Cy, hy⟩ := η.2
  obtain ⟨Cz, hz⟩ := ζ.2
  have hCy : (0 : ℝ) ≤ max Cy 0 := le_max_right _ _
  have hnorm : Tendsto
      (fun n ↦ ‖pairAt Y w (ζ : MatFam Y) (η : MatFam Y) n‖)
      (ω : Filter ℕ) (𝓝 ‖uinner (ω := ω) ζ η‖) :=
    (tendsto_ulim (exists_tendsto_pairAt hw ζ η)).norm
  refine norm_eq_zero.mp (le_antisymm ?_ (norm_nonneg _))
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  rw [zero_add]
  -- the rescaling that makes the `η` term small
  set t : ℝ := (max Cy 0 + 1) / ε with ht_def
  have ht : 0 < t := by rw [ht_def]; positivity
  have hsecond : max Cy 0 / (2 * t) ≤ ε / 2 := by
    rw [ht_def, div_le_iff₀ (by positivity)]
    have hrw : ε / 2 * (2 * ((max Cy 0 + 1) / ε)) = max Cy 0 + 1 := by
      field_simp
    rw [hrw]
    linarith
  -- and the `ζ` term is small on a set of `ω`, because `ζ` is null
  have hfirst : ∀ᶠ n in (ω : Filter ℕ),
      matMass ((ζ : MatFam Y) n) ≤ (ε / (2 * t)) * clipWeight w n :=
    hζ _ (by positivity)
  refine le_of_tendsto hnorm ?_
  filter_upwards [hfirst] with n hn
  have hscaled := norm_pairAt_le_scaled hw ht (ζ : MatFam Y) (η : MatFam Y) n
  have hclip : clipWeight w n = w n := max_eq_left (hw n)
  rw [hclip] at hn
  rcases (hw n).lt_or_eq with hposn | hzeron
  · have h1 : matMass ((ζ : MatFam Y) n) / w n ≤ ε / (2 * t) :=
      (div_le_iff₀ hposn).mpr hn
    have h2 : matMass ((η : MatFam Y) n) / w n ≤ max Cy 0 := by
      rw [div_le_iff₀ hposn]
      nlinarith [hy n, le_max_left Cy 0, hposn.le]
    have hA : t * (matMass ((ζ : MatFam Y) n) / w n) / 2 ≤ ε / 4 := by
      have hmul := mul_le_mul_of_nonneg_left h1 ht.le
      have hEq : t * (ε / (2 * t)) = ε / 2 := by
        field_simp
      rw [hEq] at hmul
      linarith
    have hB : matMass ((η : MatFam Y) n) / w n / (2 * t)
        ≤ max Cy 0 / (2 * t) := by gcongr
    linarith [hscaled, hA, hB, hsecond]
  · have hzn : (ζ : MatFam Y) n = 0 :=
      eq_zero_of_weight_eq_zero hz hzeron.symm
    have hzero : pairAt Y w (ζ : MatFam Y) (η : MatFam Y) n = 0 := by
      simp [pairAt, hzn]
    rw [hzero, norm_zero]
    exact hε.le

end

end HilbertUltraproductInner
end GroupApproximation
