import GroupApproximation.Sofic.LiteralP13HodgeCertificate
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# The spectral localization of the P13 Kazhdan Laplacian

Manuscript: `non_mf_groups_exist.tex`, Proposition `\ref{prop:literal-base-T}`
(subsection *Property (T) of the base*), **Step 1**.  The two sentences
formalized here were

> "The gap places the spectrum of `Δ` in `{0} ∪ [1/500, ∞)`."
>
> "The kernel of `Δ` is exactly the space of invariant vectors."

**Neither is printed any more.**  Commit `3a45fa60` replaced the three-step
property-`(T)` proof of `\ref{prop:literal-base-T}` with a one-paragraph
citation; see the header of `Monsters/P13CircumcenterRouteStep3.lean` for the
same note about Step 3.  The proposition and its badge are unchanged, the
quotations above are a record of the deleted text, and no badge is owed on the
theorems below.

## What is proved

`Δ` is the six-generator Kazhdan Laplacian
`ExactHodgeCertificate.generatorLaplacianOperator p13Generator ρ` of the
printed thirteen-relator presentation, in an arbitrary orthogonal
representation `ρ` on a complete real inner product space — the same operator
the certificate's quadratic gap
`LiteralP13HodgeCertificate.p13_generatorLaplacian_quadratic_gap` speaks about.

`t1_04_p13_spectrum_subset` proves the printed containment

  `spectrum ℝ Δ ⊆ {0} ∪ Set.Ici (1/500)`

with the printed constant, as an actual statement about `spectrum`.  This is
the step the P13 audit (`notes/P13_STEP_AUDIT.md`, item T1.04) marked MISSING:
the existing chain substitutes the damped Richardson/Neumann iteration of
`Kazhdan/PositiveOperatorGap.lean` and obtains a strictly weaker constant.
That development is untouched and remains the route used by
`Certificate.isKazhdanPair`; this file adds the printed spectral statement
alongside it.

## The argument

No functional calculus and no complexification is used, so the statement is
about the real spectrum of a real operator, exactly as printed.

For a scalar `μ` outside `{0} ∪ [c,∞)` the operator `μ - Δ` is bounded below:
with `n = ‖x‖`, `t = ‖Δx‖`, `a = ⟪x,Δx⟫`,

  `‖Δx - μx‖² = t² - 2μa + μ²n²`,

and the two facts `0 ≤ a`, `c·a ≤ t²` supplied by the certificate, together
with Cauchy–Schwarz `a ≤ n·t`, force

  `‖Δx - μx‖ ≥ min |μ| (c - μ) · ‖x‖`.

A symmetric operator on a complete space that is bounded below is a unit: it
is injective with closed range (`AntilipschitzWith`), and its range is dense
because `(range B)ᗮ = ker B = ⊥` by `LinearMap.IsSymmetric.orthogonal_range`.
Hence `μ ∉ spectrum ℝ Δ`.

The arithmetic splits into the four regimes that the extremal configurations
of the quadratic actually require: `μ < 0`; `0 < 2μ ≤ c`; `c < 2μ < 2c` with
`t ≤ cn`; and `t > cn`.  Only the last uses Cauchy–Schwarz, and only the third
needs the certificate bound rescaled by `c`.
-/

namespace GroupApproximation
namespace P13SpectralGap

open ExactHodgeCertificate LiteralP13Presentation LiteralP13HodgeCertificate

universe u v

section Abstract

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real-arithmetic core of the spectral localization.

With `n = ‖x‖`, `t = ‖Ax‖`, `a = ⟪x,Ax⟫` for a positive symmetric operator `A`
satisfying `c·a ≤ t²`, and `μ` a scalar with `μ ≠ 0` and `μ < c`, the
quadratic `t² - 2μa + μ²n²` — which is `‖Ax - μx‖²` — is at least `(δn)²` for
`δ = min |μ| (c-μ)`.  Everything is multiplied through by `c > 0` once, which
is what the regime `c/2 < μ < c` genuinely needs. -/
theorem quadraticGap_arith {c μ n t a δ : ℝ}
    (hc : 0 < c) (hμc : μ < c) (hμ0 : μ ≠ 0)
    (hn0 : 0 ≤ n) (ht0 : 0 ≤ t) (ha0 : 0 ≤ a)
    (hgap : c * a ≤ t ^ 2) (hcs : a ≤ n * t)
    (hδ : δ = min |μ| (c - μ)) :
    (δ * n) ^ 2 ≤ t ^ 2 - 2 * (μ * a) + μ ^ 2 * n ^ 2 := by
  have habs : 0 < |μ| := abs_pos.mpr hμ0
  have hcμ : 0 < c - μ := sub_pos.mpr hμc
  have hδ0 : 0 < δ := by rw [hδ]; exact lt_min habs hcμ
  have hδabs : δ ≤ |μ| := by rw [hδ]; exact min_le_left _ _
  have hδcμ : δ ≤ c - μ := by rw [hδ]; exact min_le_right _ _
  clear hδ
  have hδsqμ : δ ^ 2 ≤ μ ^ 2 := by
    have h : δ ^ 2 ≤ |μ| ^ 2 := by
      linarith [mul_le_mul_of_nonneg_left hδabs hδ0.le,
        mul_le_mul_of_nonneg_left hδabs (abs_nonneg μ)]
    rwa [sq_abs] at h
  have hδsqc : δ ^ 2 ≤ (c - μ) ^ 2 := by
    linarith [mul_le_mul_of_nonneg_left hδcμ hδ0.le,
      mul_le_mul_of_nonneg_left hδcμ hcμ.le]
  have hn2 : (0 : ℝ) ≤ n ^ 2 := sq_nonneg n
  have key : c * ((δ * n) ^ 2) ≤ c * (t ^ 2 - 2 * (μ * a) + μ ^ 2 * n ^ 2) := by
    rcases lt_or_gt_of_ne hμ0 with hneg | hpos
    · -- `μ < 0`: positivity of the quadratic form already suffices.
      have h1 : c * (δ ^ 2 * n ^ 2) ≤ c * (μ ^ 2 * n ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hδsqμ hn2) hc.le
      have h2 : (0 : ℝ) ≤ c * t ^ 2 := mul_nonneg hc.le (sq_nonneg t)
      have h3 : (0 : ℝ) ≤ c * (-μ * a) :=
        mul_nonneg hc.le (mul_nonneg (by linarith) ha0)
      nlinarith [h1, h2, h3]
    · rcases le_or_gt t (c * n) with hsmall | hbig
      · rcases le_or_gt (2 * μ) c with hhalf | hhalf
        · -- `2μ ≤ c`: the gap alone dominates the cross term.
          have h1 : c * (δ ^ 2 * n ^ 2) ≤ c * (μ ^ 2 * n ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hδsqμ hn2) hc.le
          have h4 : c * (2 * μ * a) ≤ c * t ^ 2 :=
            mul_le_mul_of_nonneg_left
              ((mul_le_mul_of_nonneg_right hhalf ha0).trans hgap) hc.le
          nlinarith [h1, h4]
        · -- `c < 2μ` and `t ≤ cn`: the minimum sits at `t = cn`.
          have hts : (0 : ℝ) ≤ (c * n - t) * (c * n + t) :=
            mul_nonneg (by linarith) (by linarith)
          have h5 : c * (δ ^ 2 * n ^ 2) ≤ c * ((c - μ) ^ 2 * n ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hδsqc hn2) hc.le
          have h6 : 2 * μ * (c * a) ≤ 2 * μ * t ^ 2 :=
            mul_le_mul_of_nonneg_left hgap (by linarith)
          have h7 : (0 : ℝ) ≤ (2 * μ - c) * ((c * n - t) * (c * n + t)) :=
            mul_nonneg (by linarith) hts
          nlinarith [h5, h6, h7]
      · -- `t > cn`: Cauchy–Schwarz, and the quadratic is a shifted square.
        have hμn : μ * n ≤ c * n := mul_le_mul_of_nonneg_right hμc.le hn0
        have hcμpos : (0 : ℝ) ≤ 2 * c * μ :=
          mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc.le) hpos.le
        have h5 : c * (δ ^ 2 * n ^ 2) ≤ c * ((c - μ) ^ 2 * n ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hδsqc hn2) hc.le
        have h8 : (0 : ℝ) ≤ 2 * c * μ * (n * t - a) :=
          mul_nonneg hcμpos (by linarith)
        have h9 : (0 : ℝ) ≤
            (t - μ * n - (c - μ) * n) * (t - μ * n + (c - μ) * n) :=
          mul_nonneg (by linarith) (by linarith)
        have h10 : (0 : ℝ) ≤
            c * ((t - μ * n - (c - μ) * n) * (t - μ * n + (c - μ) * n)) :=
          mul_nonneg hc.le h9
        nlinarith [h5, h8, h10]
  exact le_of_mul_le_mul_left key hc

/-- A positive symmetric operator with the quadratic gap `c⟪x,Ax⟫ ≤ ‖Ax‖²` is
bounded below by `min |μ| (c-μ)` after subtracting any scalar `μ ≠ 0` with
`μ < c`.  This is the vector-level content of the printed sentence "the gap
places the spectrum of `Δ` in `{0} ∪ [1/500,∞)`". -/
theorem norm_sub_smul_lower_bound
    (A : E →L[ℝ] E) {c μ : ℝ} (hc : 0 < c)
    (henergy : ∀ y : E, 0 ≤ PositiveOperatorGap.energy A y)
    (hgap : ∀ y : E, c * PositiveOperatorGap.energy A y ≤ ‖A y‖ ^ 2)
    (hμc : μ < c) (hμ0 : μ ≠ 0) (x : E) :
    min |μ| (c - μ) * ‖x‖ ≤ ‖A x - μ • x‖ := by
  have ha0 : (0 : ℝ) ≤ inner ℝ x (A x) := henergy x
  have hgx : c * inner ℝ x (A x) ≤ ‖A x‖ ^ 2 := hgap x
  have hcomm : inner ℝ (A x) x = inner ℝ x (A x) := real_inner_comm x (A x)
  have h1 : ‖A x - μ • x‖ ^ 2
      = ‖A x‖ ^ 2 - 2 * inner ℝ (A x) (μ • x) + ‖μ • x‖ ^ 2 :=
    norm_sub_sq_real (A x) (μ • x)
  have h2 : inner ℝ (A x) (μ • x) = μ * inner ℝ x (A x) := by
    rw [real_inner_smul_right, hcomm]
  have h3 : ‖μ • x‖ ^ 2 = μ ^ 2 * ‖x‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hexp : ‖A x - μ • x‖ ^ 2
      = ‖A x‖ ^ 2 - 2 * (μ * inner ℝ x (A x)) + μ ^ 2 * ‖x‖ ^ 2 := by
    rw [h1, h2, h3]
  have hcore : (min |μ| (c - μ) * ‖x‖) ^ 2
      ≤ ‖A x‖ ^ 2 - 2 * (μ * inner ℝ x (A x)) + μ ^ 2 * ‖x‖ ^ 2 :=
    quadraticGap_arith hc hμc hμ0 (norm_nonneg x) (norm_nonneg (A x)) ha0 hgx
      (real_inner_le_norm x (A x)) rfl
  have hsq : (min |μ| (c - μ) * ‖x‖) ^ 2 ≤ ‖A x - μ • x‖ ^ 2 := by
    rw [hexp]; exact hcore
  have hnn : 0 ≤ min |μ| (c - μ) * ‖x‖ :=
    mul_nonneg (le_of_lt (lt_min (abs_pos.mpr hμ0) (sub_pos.mpr hμc)))
      (norm_nonneg x)
  exact (sq_le_sq₀ hnn (norm_nonneg _)).mp hsq

/-- A symmetric continuous operator on a complete real inner product space
which is bounded below is invertible.

Bounded below gives injectivity and, through `AntilipschitzWith`, closed
range; symmetry gives `(range B)ᗮ = ker B = ⊥`, hence dense range. -/
theorem isUnit_of_isSymmetric_of_lower_bound [CompleteSpace E]
    (B : E →L[ℝ] E) (hsymm : ∀ y z : E, inner ℝ (B y) z = inner ℝ y (B z))
    {δ : ℝ} (hδ : 0 < δ) (hb : ∀ y : E, δ * ‖y‖ ≤ ‖B y‖) :
    IsUnit B := by
  have hsym : LinearMap.IsSymmetric (B : E →ₗ[ℝ] E) := by
    intro y z
    simpa using hsymm y z
  have hker : LinearMap.ker (B : E →ₗ[ℝ] E) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro y hy
    have hBy : B y = 0 := by simpa using hy
    have hb' : δ * ‖y‖ ≤ 0 := by
      have h := hb y
      rwa [hBy, norm_zero] at h
    have hy0 : ‖y‖ = 0 :=
      le_antisymm (by nlinarith [norm_nonneg y]) (norm_nonneg y)
    exact norm_eq_zero.mp hy0
  have hcoe : (((⟨δ, hδ.le⟩ : NNReal)⁻¹ : NNReal) : ℝ) = δ⁻¹ := rfl
  have hanti : AntilipschitzWith (⟨δ, hδ.le⟩ : NNReal)⁻¹ B := by
    refine B.antilipschitz_of_bound (K := (⟨δ, hδ.le⟩ : NNReal)⁻¹) fun y ↦ ?_
    rw [hcoe, inv_mul_eq_div, le_div_iff₀ hδ, mul_comm]
    exact hb y
  rw [ContinuousLinearMap.isUnit_iff_bijective,
    ContinuousLinearMap.bijective_iff_dense_range_and_antilipschitz]
  refine ⟨?_, ⟨_, hanti⟩⟩
  have hperp : (B.range)ᗮ = ⊥ := hsym.orthogonal_range.trans hker
  exact Submodule.topologicalClosure_eq_top_iff.mpr hperp

/-- **The spectral localization.**  A positive symmetric operator on a complete
real inner product space obeying the quadratic gap `c⟪x,Ax⟫ ≤ ‖Ax‖²` has real
spectrum inside `{0} ∪ [c,∞)`.

This is the abstract form of the manuscript's Step 1 sentence.  Note that it
contains the assertion that there is no negative spectrum as well: for `μ < 0`
positivity of the form alone gives `‖Ax - μx‖ ≥ |μ|·‖x‖`. -/
theorem spectrum_subset_zero_union_Ici [CompleteSpace E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hsymm : ∀ y z : E, inner ℝ (A y) z = inner ℝ y (A z))
    (henergy : ∀ y : E, 0 ≤ PositiveOperatorGap.energy A y)
    (hgap : ∀ y : E, c * PositiveOperatorGap.energy A y ≤ ‖A y‖ ^ 2) :
    spectrum ℝ A ⊆ {0} ∪ Set.Ici c := by
  intro μ hμ
  by_contra hcon
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_Ici, not_or,
    not_le] at hcon
  obtain ⟨hμ0, hμc⟩ := hcon
  apply spectrum.mem_iff.mp hμ
  have hBapply : ∀ y : E,
      (algebraMap ℝ (E →L[ℝ] E) μ - A) y = μ • y - A y := by
    intro y; simp
  have hBsymm : ∀ y z : E,
      inner ℝ ((algebraMap ℝ (E →L[ℝ] E) μ - A) y) z
        = inner ℝ y ((algebraMap ℝ (E →L[ℝ] E) μ - A) z) := by
    intro y z
    rw [hBapply, hBapply, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, hsymm y z]
  have hBnorm : ∀ y : E,
      min |μ| (c - μ) * ‖y‖ ≤ ‖(algebraMap ℝ (E →L[ℝ] E) μ - A) y‖ := by
    intro y
    have hrev : ‖(algebraMap ℝ (E →L[ℝ] E) μ - A) y‖ = ‖A y - μ • y‖ := by
      rw [hBapply, norm_sub_rev]
    rw [hrev]
    exact norm_sub_smul_lower_bound A hc henergy hgap hμc hμ0 y
  exact isUnit_of_isSymmetric_of_lower_bound _ hBsymm
    (lt_min (abs_pos.mpr hμ0) (sub_pos.mpr hμc)) hBnorm

/-- The kernel of a generator Laplacian is exactly the space of vectors fixed
by the whole group, when the tuple generates.  The nontrivial inclusion is
`ExactHodgeCertificate.invariant_of_generatorLaplacian_eq_zero`; the converse
is the observation that a fixed vector kills every summand. -/
theorem ker_generatorLaplacian_eq_invariants
    {G : Type u} [Group G] {I : Type*} [Fintype I] (s : I → G)
    (hgen : Subgroup.closure (Set.range s) = ⊤)
    {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (rho : G →* (F ≃ₗᵢ[ℝ] F)) :
    {x : F | generatorLaplacianOperator s rho x = 0}
      = {x : F | ∀ g : G, rho g x = x} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hx
    exact invariant_of_generatorLaplacian_eq_zero s hgen rho x hx
  · intro hx
    rw [generatorLaplacianOperator_apply]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [hx (s i)]
    simp

end Abstract

section P13

variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Manuscript Step 1, item T1.04**: *"The gap places the spectrum of `Δ` in
`{0} ∪ [1/500, ∞)`."*

`Δ` is the six-generator Kazhdan Laplacian of the printed thirteen-relator
presentation in an arbitrary orthogonal representation, and the constant is
the printed `1/500`, delivered by the exact sum-of-squares certificate as
`c - r = 1/250 - 1/500`. -/
theorem t1_04_p13_spectrum_subset [CompleteSpace F]
    (rho : P13 →* (F ≃ₗᵢ[ℝ] F)) :
    spectrum ℝ (generatorLaplacianOperator p13Generator rho)
      ⊆ {0} ∪ Set.Ici (1 / 500 : ℝ) := by
  refine spectrum_subset_zero_union_Ici
    (generatorLaplacianOperator p13Generator rho) (c := (1 / 500 : ℝ))
    (by norm_num) ?_ ?_ ?_
  · intro y z
    exact generatorLaplacian_symmetric p13Generator rho y z
  · intro y
    rw [generatorLaplacian_energy p13Generator rho y]
    exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  · intro y
    exact p13_generatorLaplacian_quadratic_gap rho y

/-- **Manuscript Step 1, item T1.05**: *"The kernel of `Δ` is exactly the space
of invariant vectors."*  Stated as the printed equality, not as the single
inclusion the Kazhdan argument happens to consume. -/
theorem t1_05_p13_ker_eq_invariants (rho : P13 →* (F ≃ₗᵢ[ℝ] F)) :
    {x : F | generatorLaplacianOperator p13Generator rho x = 0}
      = {x : F | ∀ g : P13, rho g x = x} :=
  ker_generatorLaplacian_eq_invariants p13Generator closure_range_p13Generator
    rho

end P13

end P13SpectralGap
end GroupApproximation
