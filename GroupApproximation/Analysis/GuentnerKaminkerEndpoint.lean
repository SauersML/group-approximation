import GroupApproximation.Analysis.RoeSquareRoot
import GroupApproximation.Analysis.GuentnerKaminker

/-!
# Guentner--Kaminker, unconditionally

`Analysis/GuentnerKaminker.lean` proves Theorem 3.2's group side modulo one
named hypothesis, `IsRoeSquareApproximable`.  This module discharges it, and so
states the theorem with no hypotheses beyond the mathematics:

> a finitely generated group whose Hilbert space compression exceeds `1/2` has
> Yu's property A.

The chain, all of it proved in this repository:

| step | module |
|---|---|
| exponential growth of balls | `Algebra/WordMetricBall.lean` |
| estimate (14) | `Analysis/CoarseCompression.lean` |
| Schoenberg | `Analysis/SchoenbergKernel.lean` |
| finite-width kernels are operators | `Analysis/L2KernelOperator.lean` |
| `Op(u)` is positive and lies in `C*_u(Γ)` | `Analysis/GaussianRoeOperator.lean` |
| `√(Op u)` and the finite-width Gram approximation | `Analysis/RoeSquareRoot.lean` |
| `ℓ²` columns give Yu's measures | `Analysis/PropertyASquareWitness.lean` |

## Why the Gram condition is stated over `ℂ`

`GuentnerKaminker.IsRoeSquareApproximable` asks for a **real** family `w` with
`Σ w(s,x) w(t,x) ≈ u(s,t)`.  The columns of a finite-propagation approximant to
`√(Op u)` are complex, and there is no reason for them to be real.  Passing to
moduli is fine for the *witness* --- the property A weights are `|ζ(x)|²`, and
`| ‖a‖ - ‖b‖ | ≤ ‖a - b‖` only improves the `ℓ²` displacement --- but it
destroys the Gram *identity*, since `Σ |a||b| ≠ Σ conj(a) b`.  So the condition
is restated over `ℂ` here, and the assembly is redone with moduli.

This module and `Analysis/RoeSquareRoot.lean` have both been elaborated at the
pinned toolchain.
-/

namespace GroupApproximation
namespace GuentnerKaminkerEndpoint

open ExactnessPermanence CoarseCompression PropertyASquareWitness SchoenbergKernel
open ReducedGroupCStarTrace UniformRoe L2KernelOperator GaussianRoeOperator
open RoeSquareRoot
open scoped InnerProductSpace

universe u v

variable {G : Type u} [Group G] [DecidableEq G]
  {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## The complex Gram condition -/

/-- The complex-valued form of `GuentnerKaminker.IsRoeSquareApproximable`: the
kernel is uniformly approximated by Gram kernels of families of finite
propagation. -/
def IsRoeGramApproximable (u : G → G → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ (F : Finset G) (w : G → G → ℂ),
    (∀ s x, s⁻¹ * x ∉ F → w s x = 0) ∧
    ∀ (s t : G) (T : Finset G), (∀ x, w s x ≠ 0 → x ∈ T) → (∀ x, w t x ≠ 0 → x ∈ T) →
      ‖((u s t : ℝ) : ℂ) - ∑ x ∈ T, (starRingEnd ℂ) (w s x) * w t x‖ ≤ δ

/-! ## From the Gram condition to property A -/

/-- `| ‖a‖ - ‖b‖ | ≤ ‖a - b‖`, squared: passing to moduli does not increase the
`ℓ²` displacement. -/
theorem sq_norm_sub_norm_le (a b : ℂ) : (‖a‖ - ‖b‖) ^ 2 ≤ ‖a - b‖ ^ 2 := by
  have h : |‖a‖ - ‖b‖| ≤ ‖a - b‖ := abs_norm_sub_norm_le a b
  have h0 : (0 : ℝ) ≤ ‖a - b‖ := norm_nonneg _
  calc (‖a‖ - ‖b‖) ^ 2 = |‖a‖ - ‖b‖| ^ 2 := (sq_abs _).symm
    _ ≤ ‖a - b‖ ^ 2 := by nlinarith [abs_nonneg (‖a‖ - ‖b‖)]

omit [Group G] [DecidableEq G] in
/-- The expansion of an `ℓ²` displacement of a finite family in terms of its
Gram data. -/
theorem sum_norm_sub_sq (T : Finset G) (a b : G → ℂ) :
    ∑ x ∈ T, ‖a x - b x‖ ^ 2
      = (∑ x ∈ T, ‖a x‖ ^ 2) + (∑ x ∈ T, ‖b x‖ ^ 2)
        - 2 * (∑ x ∈ T, ((starRingEnd ℂ) (a x) * b x)).re := by
  rw [Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have h : ‖a x - b x‖ ^ 2
      = ‖a x‖ ^ 2 + ‖b x‖ ^ 2 - 2 * ((starRingEnd ℂ) (a x) * b x).re := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  simpa using h

omit [InnerProductSpace ℝ E] in
/-- **From the complex Gram condition to property A.**  This is the assembly of
`GuentnerKaminker.hasPropertyA_of_gaussianRoeApproximation`, redone with moduli
so that complex columns are allowed. -/
theorem hasPropertyA_of_gram {T : Finset G} {f : G → E} {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ x y : G, ‖f x - f y‖ ≤ C * (WordMetric.wordDist (↑T : Set G) x y : ℝ) + D)
    (hgram : ∀ κ : ℝ, 0 < κ → IsRoeGramApproximable (gaussianKernel f κ)) :
    HasPropertyA G := by
  classical
  refine hasPropertyA_of_squareWitness ?_
  intro R ε hε
  set Rad : ℕ := ∑ r ∈ R, WordMetric.wordNorm (↑T : Set G) r
  have hRad : ∀ g h : G, g⁻¹ * h ∈ R → WordMetric.wordDist (↑T : Set G) g h ≤ Rad := by
    intro g h hgh
    have hsingle := Finset.single_le_sum
      (f := fun r ↦ WordMetric.wordNorm (↑T : Set G) r) (fun i _ ↦ Nat.zero_le _) hgh
    show WordMetric.wordNorm (↑T : Set G) (g⁻¹ * h) ≤ Rad
    exact hsingle
  obtain ⟨κ, hκ, hκP⟩ :
      ∃ κ : ℝ, 0 < κ ∧ κ * (C * (Rad : ℝ) + D) ^ 2 ≤ ε ^ 2 / 8 := by
    have hε2 : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
    have hnum : (0 : ℝ) < ε ^ 2 / 8 := by linarith
    have hden : (0 : ℝ) < (C * (Rad : ℝ) + D) ^ 2 + 1 := by positivity
    have hden' : ((C * (Rad : ℝ) + D) ^ 2 + 1) ≠ 0 := ne_of_gt hden
    refine ⟨(ε ^ 2 / 8) / ((C * (Rad : ℝ) + D) ^ 2 + 1), div_pos hnum hden, ?_⟩
    have hstep : (ε ^ 2 / 8) / ((C * (Rad : ℝ) + D) ^ 2 + 1) * (C * (Rad : ℝ) + D) ^ 2
        ≤ (ε ^ 2 / 8) / ((C * (Rad : ℝ) + D) ^ 2 + 1) * ((C * (Rad : ℝ) + D) ^ 2 + 1) := by
      refine mul_le_mul_of_nonneg_left (by linarith) ?_
      positivity
    refine le_trans hstep (le_of_eq ?_)
    field_simp
  obtain ⟨δ, hδ, hδhalf, hδeps⟩ :
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ δ ≤ ε ^ 2 / 16 :=
    ⟨min (1 / 2) (ε ^ 2 / 16),
      lt_min (by norm_num) (by have := pow_pos hε 2; linarith),
      min_le_left _ _, min_le_right _ _⟩
  obtain ⟨F, w, hsupp, happ⟩ := hgram κ hκ δ hδ
  -- the translated template is a window for every column
  have hwin : ∀ g : G, ∀ x, w g x ≠ 0 → x ∈ F.image (fun s ↦ g * s) := by
    intro g x hx
    have hmemF : g⁻¹ * x ∈ F := by
      by_contra hc
      exact hx (hsupp g x hc)
    exact Finset.mem_image.mpr ⟨g⁻¹ * x, hmemF, by simp⟩
  have hdiag : ∀ (g : G) (S : Finset G),
      ∑ x ∈ S, (starRingEnd ℂ) (w g x) * w g x =
        ((∑ x ∈ S, ‖w g x‖ ^ 2 : ℝ) : ℂ) := by
    intro g S
    push_cast
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    norm_cast
  -- the columns are almost unit vectors
  have hmassabs : ∀ g : G, |1 - ∑ s ∈ F, ‖w g (g * s)‖ ^ 2| ≤ δ := by
    intro g
    have h := happ g g (F.image (fun s ↦ g * s)) (hwin g) (hwin g)
    rw [gaussianKernel_self] at h
    have hreal : ∑ x ∈ F.image (fun s ↦ g * s), ‖w g x‖ ^ 2 =
        ∑ s ∈ F, ‖w g (g * s)‖ ^ 2 :=
      sum_sq_window_eq (v := fun x ↦ ‖w g x‖) g
        (fun x hx ↦ by rw [hsupp g x hx, norm_zero])
        (fun x hx ↦ hwin g x (by
          intro hzero
          exact hx (by rw [hzero, norm_zero])))
    have hsq : ∑ x ∈ F.image (fun s ↦ g * s), (starRingEnd ℂ) (w g x) * w g x
        = ((∑ s ∈ F, ‖w g (g * s)‖ ^ 2 : ℝ) : ℂ) := by
      rw [hdiag g, hreal]
    rw [hsq] at h
    have : ‖((1 : ℝ) : ℂ) - ((∑ s ∈ F, ‖w g (g * s)‖ ^ 2 : ℝ) : ℂ)‖
        = |1 - ∑ s ∈ F, ‖w g (g * s)‖ ^ 2| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [← this]
    simpa using h
  refine ⟨{
    template := F
    vec := fun g x ↦ ‖w g x‖
    vec_eq_zero := fun g x hx ↦ by rw [hsupp g x hx, norm_zero]
    mass_lower := ?_
    mass_upper := ?_
    vec_close := ?_ }⟩
  · intro g
    have h := abs_le.mp (hmassabs g)
    linarith [h.1, h.2, hδhalf]
  · intro g
    have h := abs_le.mp (hmassabs g)
    linarith [h.1, h.2, hδhalf]
  · intro g h hgh S hSg hSh
    have hSg' : ∀ x, w g x ≠ 0 → x ∈ S := fun x hx ↦ hSg x (by simpa using hx)
    have hSh' : ∀ x, w h x ≠ 0 → x ∈ S := fun x hx ↦ hSh x (by simpa using hx)
    have hA := happ g g S hSg' hSg'
    have hB := happ h h S hSh' hSh'
    have hAB := happ g h S hSg' hSh'
    rw [gaussianKernel_self] at hA
    rw [gaussianKernel_self] at hB
    rw [hdiag g S] at hA
    rw [hdiag h S] at hB
    have hstrip : 1 - gaussianKernel f κ g h ≤ κ * (C * (Rad : ℝ) + D) ^ 2 :=
      one_sub_gaussianKernel_le hC hD hb hκ.le Rad g h (hRad g h hgh)
    -- pass to moduli, then expand
    have hmod : ∑ x ∈ S, (‖w g x‖ - ‖w h x‖) ^ 2 ≤ ∑ x ∈ S, ‖w g x - w h x‖ ^ 2 :=
      Finset.sum_le_sum fun x _ ↦ sq_norm_sub_norm_le _ _
    rw [sum_norm_sub_sq] at hmod
    -- the three Gram quantities are within `δ` of the kernel
    have hArewrite : (((1 : ℝ) : ℂ) - ((∑ x ∈ S, ‖w g x‖ ^ 2 : ℝ) : ℂ)) =
        ((1 - ∑ x ∈ S, ‖w g x‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      rfl
    have hBrewrite : (((1 : ℝ) : ℂ) - ((∑ x ∈ S, ‖w h x‖ ^ 2 : ℝ) : ℂ)) =
        ((1 - ∑ x ∈ S, ‖w h x‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hArewrite, Complex.norm_real, Real.norm_eq_abs] at hA
    rw [hBrewrite, Complex.norm_real, Real.norm_eq_abs] at hB
    have h3 : ‖((gaussianKernel f κ g h : ℝ) : ℂ)
        - ∑ x ∈ S, (starRingEnd ℂ) (w g x) * w h x‖ ≤ δ := hAB
    have h3re : |gaussianKernel f κ g h
        - (∑ x ∈ S, (starRingEnd ℂ) (w g x) * w h x).re| ≤ δ := by
      refine le_trans ?_ h3
      have := Complex.abs_re_le_norm
        (((gaussianKernel f κ g h : ℝ) : ℂ) - ∑ x ∈ S, (starRingEnd ℂ) (w g x) * w h x)
      simpa using this
    have h3' := abs_le.mp h3re
    have hsq0 : (0 : ℝ) ≤ ε ^ 2 := sq_nonneg ε
    have hAre : |1 - (∑ x ∈ S, ‖w g x‖ ^ 2)| ≤ δ := hA
    have hBre : |1 - (∑ x ∈ S, ‖w h x‖ ^ 2)| ≤ δ := hB
    have hA' := abs_le.mp hAre
    have hB' := abs_le.mp hBre
    linarith [hmod, hA'.1, hA'.2, hB'.1, hB'.2, h3'.1, h3'.2, hstrip, hκP, hδeps, hsq0]

/-! ## The Gram condition, discharged -/

/-- **The Gaussian kernel is approximable by finite-propagation Gram kernels.**
This is the operator step of Guentner--Kaminker's Theorem 3.2, discharged:
`Op(u)` is a positive element of `C*_u(Γ)`, its square root is a norm limit of
finite-propagation operators, and the Gram kernel of such an approximant is
uniformly close to `u`.

The inversion `x ↦ x⁻¹` is where the two conventions meet: `GaussianRoeOperator`
works with the right-invariant displacement `s t⁻¹`, which is what makes the
`ℓ¹`-over-the-window bound converge, while property A is stated left-invariantly.
Reading the columns backwards converts one to the other. -/
theorem isRoeGramApproximable {T : Finset G}
    (hT : WordMetric.IsSymmetricGeneratingSet (↑T : Set G)) {f : G → E} {β : ℝ}
    (hβ : 1 / 2 < β) {r₀ : ℕ} (hr₁ : 1 ≤ r₀)
    (hr₀ : ∀ x y : G, r₀ ≤ WordMetric.wordDist (↑T : Set G) x y →
      ((WordMetric.wordDist (↑T : Set G) x y : ℝ)) ^ β ≤ ‖f x - f y‖)
    {κ : ℝ} (hκ : 0 < κ) :
    IsRoeGramApproximable (gaussianKernel f κ) := by
  classical
  intro δ hδ
  obtain ⟨K, hmem, hpos, hcoeff⟩ := exists_positive_roeOperator hT hβ hr₀ hκ hr₁
  have hKnn : 0 ≤ K := (ContinuousLinearMap.nonneg_iff_isPositive K).mpr hpos
  obtain ⟨S, W, hS, hclose⟩ := exists_finiteWidth_gram hmem hKnn hδ
  refine ⟨S.image (fun a ↦ a⁻¹), fun s x ↦ matrixCoeff G W (x⁻¹) (s⁻¹), ?_, ?_⟩
  · -- propagation, read backwards
    intro s x hx
    by_contra hne
    refine hx ?_
    have hprop : x⁻¹ * (s⁻¹)⁻¹ ∈ (S : Set G) := hS _ _ hne
    have hmem' : x⁻¹ * s ∈ S := by simpa using hprop
    exact Finset.mem_image.mpr ⟨x⁻¹ * s, hmem', by group⟩
  · intro s t T' hT1 hT2
    -- the Gram sum is the matrix of `star W * W`, read backwards
    set φ : G → ℂ := fun y ↦
      (starRingEnd ℂ) (matrixCoeff G W y (s⁻¹)) * matrixCoeff G W y (t⁻¹) with hφ
    have hvanish_t : ∀ y : G, y ∉ S.image (fun a ↦ a * t⁻¹) → φ y = 0 := by
      intro y hy
      have hz : matrixCoeff G W y (t⁻¹) = 0 := by
        by_contra hne
        refine hy (Finset.mem_image.mpr ⟨y * t, ?_, by group⟩)
        simpa using hS y t⁻¹ hne
      rw [hφ]
      change (starRingEnd ℂ) (matrixCoeff G W y (s⁻¹)) * matrixCoeff G W y (t⁻¹) = 0
      rw [hz, mul_zero]
    have hvanish_T : ∀ y : G, y ∉ T'.image (fun x ↦ x⁻¹) → φ y = 0 := by
      intro y hy
      have hz : matrixCoeff G W y (t⁻¹) = 0 := by
        by_contra hne
        refine hy (Finset.mem_image.mpr ⟨y⁻¹, hT2 y⁻¹ ?_, by simp⟩)
        simpa using hne
      rw [hφ]
      change (starRingEnd ℂ) (matrixCoeff G W y (s⁻¹)) * matrixCoeff G W y (t⁻¹) = 0
      rw [hz, mul_zero]
    have hsum_eq : ∑ x ∈ T', (starRingEnd ℂ) (matrixCoeff G W (x⁻¹) (s⁻¹))
          * matrixCoeff G W (x⁻¹) (t⁻¹)
        = matrixCoeff G (star W * W) (s⁻¹) (t⁻¹) := by
      have hinj : Set.InjOn (fun x : G ↦ x⁻¹) (T' : Set G) :=
        fun a _ b _ hab ↦ inv_injective hab
      have hleft : ∑ x ∈ T', φ (x⁻¹) = ∑ y ∈ T'.image (fun x : G ↦ x⁻¹), φ y :=
        (Finset.sum_image hinj).symm
      have hright : matrixCoeff G (star W * W) (s⁻¹) (t⁻¹)
          = ∑ y ∈ S.image (fun a ↦ a * t⁻¹), φ y := by
        rw [matrixCoeff_mul (star W) W hS (s⁻¹) (t⁻¹)]
        refine Finset.sum_congr rfl fun y _ ↦ ?_
        rw [matrixCoeff_star, hφ]
        ring
      have hcommon : ∑ y ∈ T'.image (fun x : G ↦ x⁻¹), φ y
          = ∑ y ∈ S.image (fun a ↦ a * t⁻¹), φ y := by
        have h1 : ∑ y ∈ T'.image (fun x : G ↦ x⁻¹), φ y
            = ∑ y ∈ T'.image (fun x : G ↦ x⁻¹) ∪ S.image (fun a ↦ a * t⁻¹), φ y :=
          Finset.sum_subset Finset.subset_union_left fun y _ hy ↦ hvanish_T y hy
        have h2 : ∑ y ∈ S.image (fun a ↦ a * t⁻¹), φ y
            = ∑ y ∈ T'.image (fun x : G ↦ x⁻¹) ∪ S.image (fun a ↦ a * t⁻¹), φ y :=
          Finset.sum_subset Finset.subset_union_right fun y _ hy ↦ hvanish_t y hy
        rw [h1, h2]
      rw [hleft, hcommon, hright]
    rw [hsum_eq]
    have hker : ((gaussianKernel f κ s t : ℝ) : ℂ) = matrixCoeff G K (s⁻¹) (t⁻¹) := by
      rw [hcoeff (s⁻¹) (t⁻¹), invGaussian]
      simp
    rw [hker]
    exact hclose (s⁻¹) (t⁻¹)

/-! ## The theorem -/

/-- **Guentner--Kaminker, Theorem 3.2, group side --- unconditionally.**

If a finitely generated group admits a large-scale Lipschitz map into a real
inner product space with compression exponent above `1/2`, then it has Yu's
property A.  There are no hypotheses beyond that: Schoenberg's theorem, the
Schur-test replacement, positivity, the square root in `C*_u(Γ)` and the
finite-width approximation are all proved in this repository.

What remains outside is only the crossover from property A to exactness of
`C⋆_red(Γ)`, which is Ozawa's theorem and is the standing gap `E.4` / `SO.16`. -/
theorem hasPropertyA_of_compressionExceeds_half {T : Finset G}
    (hT : WordMetric.IsSymmetricGeneratingSet (↑T : Set G))
    (hcomp : CompressionExceeds (↑T : Set G) (1 / 2) E) :
    HasPropertyA G := by
  obtain ⟨f, β, hβ, hlip, hcompf⟩ := hcomp
  obtain ⟨C, D, hC, hD, hb⟩ := hlip
  obtain ⟨r₀, hr₀⟩ := hcompf
  refine hasPropertyA_of_gram hC hD hb fun κ hκ ↦ ?_
  refine isRoeGramApproximable hT hβ (r₀ := max r₀ 1) (le_max_right _ _) ?_ hκ
  intro x y hxy
  exact hr₀ x y (le_trans (le_max_left _ _) hxy)

end GuentnerKaminkerEndpoint
end GroupApproximation
