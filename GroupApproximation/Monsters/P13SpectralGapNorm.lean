import GroupApproximation.Monsters.P13SpectralGap

/-!
# The sharp displacement constant behind the P13 spectral gap

Manuscript: `non_mf_groups_exist.tex`, Proposition `prop:literal-base-T`,
Step 1 (the sentences formalized in `Monsters/P13SpectralGap.lean`).

`Monsters/P13SpectralGap.lean` proves the printed containment
`spectrum ℝ Δ ⊆ {0} ∪ [1/500, ∞)`.  This file extracts what that containment
is *for*: in a representation with no nonzero invariant vector, `0` is not in
the spectrum either, so

  `‖Δ x‖ ≥ (1/500) ‖x‖`   and   `spectrum ℝ Δ ⊆ [1/500, ∞)`,

with the printed constant and no loss.

This is the sharp form of `Kazhdan/PositiveOperatorGap.norm_le_of_quadratic_gap`,
whose damped Richardson/Neumann iteration delivers the strictly smaller
constant `c(1 - √(1 - c/M))` (for the P13 Laplacian: `c = 1/500`, `M = 24`,
so roughly `4·10⁻⁸` instead of `2·10⁻³`).  That development is untouched and
still drives `Certificate.isKazhdanPair`; it is *used* here, but only to
supply invertibility, after which the constant is recovered exactly.

## The argument

Three ingredients, all elementary and all over the reals:

1. `norm_le_of_quadratic_gap` bounds `Δ` below by *some* positive constant when
   the kernel is trivial, so `Δ` is bounded below and symmetric, hence a unit
   (`P13SpectralGap.isUnit_of_isSymmetric_of_lower_bound`).  In particular `Δ`
   is surjective.  Note that surjectivity is exactly the step the printed
   sentence hides: the containment `spectrum ⊆ {0} ∪ [c,∞)` alone does not
   exclude `0` from the spectrum, it only makes `0` isolated.
2. Cauchy–Schwarz for the positive semi-definite form `⟪·, Δ·⟫`
   (`inner_sq_le_energy_mul_energy`), proved by the discriminant of
   `t ↦ ⟪u + tv, Δ(u + tv)⟫`.
3. Given `w`, choose `z` with `Δz = w`.  Then `⟪Δw, z⟫ = ⟪w, Δz⟫ = ‖w‖²`, so
   Cauchy–Schwarz gives `‖w‖⁴ ≤ ⟪w,Δw⟫·⟪z,Δz⟫`, and the certificate gap
   applied at `w` and at `z` turns this into `c²‖w‖⁴ ≤ ‖Δw‖²‖w‖²`.
-/

namespace GroupApproximation
namespace P13SpectralGapNorm

open ExactHodgeCertificate LiteralP13Presentation LiteralP13HodgeCertificate

universe u v

section Abstract

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The discriminant step: a real quadratic `t ↦ a + 2tb + t²d` with `d > 0`
that is everywhere nonnegative has nonpositive discriminant. -/
theorem discriminant_nonneg {a b d : ℝ} (hd : 0 < d)
    (h : ∀ t : ℝ, 0 ≤ a + 2 * t * b + t ^ 2 * d) : b ^ 2 ≤ a * d := by
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hat := h (-b / d)
  have hkey : d * (a + 2 * (-b / d) * b + (-b / d) ^ 2 * d) = a * d - b ^ 2 := by
    field_simp
    ring
  have hmul : 0 ≤ d * (a + 2 * (-b / d) * b + (-b / d) ^ 2 * d) :=
    mul_nonneg hd.le hat
  rw [hkey] at hmul
  linarith

/-- **Cauchy–Schwarz for the quadratic form of a positive symmetric operator.**

If `A` is symmetric with `0 ≤ ⟪y, A y⟫` for all `y`, then
`⟪A u, v⟫² ≤ ⟪u, A u⟫ ⟪v, A v⟫`.  Only the nondegenerate case is stated,
which is the one used; it is proved from the discriminant of the nonnegative
quadratic `t ↦ ⟪u + t v, A (u + t v)⟫`. -/
theorem inner_sq_le_energy_mul_energy (A : E →L[ℝ] E)
    (hsymm : ∀ y z : E, inner ℝ (A y) z = inner ℝ y (A z))
    (henergy : ∀ y : E, 0 ≤ PositiveOperatorGap.energy A y)
    (u v : E) (hv : 0 < PositiveOperatorGap.energy A v) :
    inner ℝ (A u) v ^ 2
      ≤ PositiveOperatorGap.energy A u * PositiveOperatorGap.energy A v := by
  show inner ℝ (A u) v ^ 2 ≤ inner ℝ u (A u) * inner ℝ v (A v)
  have hv' : (0 : ℝ) < inner ℝ v (A v) := hv
  have hs1 : inner ℝ u (A v) = inner ℝ (A u) v := (hsymm u v).symm
  have hs2 : inner ℝ v (A u) = inner ℝ (A u) v := real_inner_comm (A u) v
  have hquad : ∀ t : ℝ, 0 ≤ inner ℝ u (A u) + 2 * t * inner ℝ (A u) v
      + t ^ 2 * inner ℝ v (A v) := by
    intro t
    have hpos : (0 : ℝ) ≤ inner ℝ (u + t • v) (A (u + t • v)) :=
      henergy (u + t • v)
    have hAv : A (u + t • v) = A u + t • A v := by
      rw [map_add, ContinuousLinearMap.map_smul]
    have hexp : inner ℝ (u + t • v) (A (u + t • v))
        = inner ℝ u (A u) + 2 * t * inner ℝ (A u) v
          + t ^ 2 * inner ℝ v (A v) := by
      simp only [hAv, inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, hs1, hs2]
      ring
    rw [hexp] at hpos
    exact hpos
  exact discriminant_nonneg hv' hquad

/-- A positive symmetric operator with a quadratic gap and a trivial kernel is
invertible on a complete space.  The Richardson/Neumann iteration of
`Kazhdan/PositiveOperatorGap.lean` supplies a (weak) lower bound, and a
symmetric operator bounded below is a unit. -/
theorem isUnit_of_quadratic_gap [CompleteSpace E]
    (A : E →L[ℝ] E) {c M : ℝ} (hc : 0 < c) (hM : 0 < M) (hcM : c ≤ M)
    (hsymm : ∀ y z : E, inner ℝ (A y) z = inner ℝ y (A z))
    (henergy : ∀ y : E, 0 ≤ PositiveOperatorGap.energy A y)
    (hlower : ∀ y : E, c * PositiveOperatorGap.energy A y ≤ ‖A y‖ ^ 2)
    (hformUpper : ∀ y : E, PositiveOperatorGap.energy A y ≤ M * ‖y‖ ^ 2)
    (hnormUpper : ∀ y : E, ‖A y‖ ^ 2 ≤ M * PositiveOperatorGap.energy A y)
    (hker : ∀ y : E, A y = 0 → y = 0) :
    IsUnit A := by
  have hratio0 : 0 ≤ 1 - c / M := by
    rw [sub_nonneg, div_le_one hM]
    exact hcM
  have hsqrtNonneg : 0 ≤ Real.sqrt (1 - c / M) := Real.sqrt_nonneg _
  have hsqrtSq : Real.sqrt (1 - c / M) ^ 2 = 1 - c / M := Real.sq_sqrt hratio0
  have hlt : 1 - c / M < 1 := sub_lt_self _ (div_pos hc hM)
  have hsqrt1 : Real.sqrt (1 - c / M) < 1 := by
    nlinarith [sq_nonneg (Real.sqrt (1 - c / M) - 1)]
  have hK : 0 < c * (1 - Real.sqrt (1 - c / M)) :=
    mul_pos hc (sub_pos.mpr hsqrt1)
  have hKne : c * (1 - Real.sqrt (1 - c / M)) ≠ 0 := ne_of_gt hK
  have hbdd : ∀ y : E, (c * (1 - Real.sqrt (1 - c / M))) * ‖y‖ ≤ ‖A y‖ := by
    intro y
    have h := PositiveOperatorGap.norm_le_of_quadratic_gap A hc hM hcM hsymm
      henergy hlower hformUpper hnormUpper hker y
    calc (c * (1 - Real.sqrt (1 - c / M))) * ‖y‖
        ≤ (c * (1 - Real.sqrt (1 - c / M))) *
            ((c * (1 - Real.sqrt (1 - c / M)))⁻¹ * ‖A y‖) :=
          mul_le_mul_of_nonneg_left h hK.le
      _ = ‖A y‖ := by rw [← mul_assoc, mul_inv_cancel₀ hKne, one_mul]
  exact P13SpectralGap.isUnit_of_isSymmetric_of_lower_bound A hsymm hK hbdd

/-- **The sharp lower bound.**  Under exactly the hypotheses of
`PositiveOperatorGap.norm_le_of_quadratic_gap`, the operator satisfies
`c ‖x‖ ≤ ‖A x‖` — the constant the printed spectral localization predicts,
not the smaller Richardson constant. -/
theorem norm_lower_bound_of_quadratic_gap [CompleteSpace E]
    (A : E →L[ℝ] E) {c M : ℝ} (hc : 0 < c) (hM : 0 < M) (hcM : c ≤ M)
    (hsymm : ∀ y z : E, inner ℝ (A y) z = inner ℝ y (A z))
    (henergy : ∀ y : E, 0 ≤ PositiveOperatorGap.energy A y)
    (hlower : ∀ y : E, c * PositiveOperatorGap.energy A y ≤ ‖A y‖ ^ 2)
    (hformUpper : ∀ y : E, PositiveOperatorGap.energy A y ≤ M * ‖y‖ ^ 2)
    (hnormUpper : ∀ y : E, ‖A y‖ ^ 2 ≤ M * PositiveOperatorGap.energy A y)
    (hker : ∀ y : E, A y = 0 → y = 0) (w : E) :
    c * ‖w‖ ≤ ‖A w‖ := by
  have hunit : IsUnit A :=
    isUnit_of_quadratic_gap A hc hM hcM hsymm henergy hlower hformUpper
      hnormUpper hker
  have hbij : Function.Bijective A :=
    ContinuousLinearMap.isUnit_iff_bijective.mp hunit
  obtain ⟨z, hz⟩ := hbij.2 w
  rcases eq_or_lt_of_le (henergy z) with hzero | hzpos
  · -- Degenerate case: a null-energy preimage forces `w = 0`.
    have h1 : ‖A z‖ ^ 2 ≤ 0 := by
      have h := hnormUpper z
      rwa [← hzero, mul_zero] at h
    have hsq0 : ‖A z‖ ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
    have h2 : A z = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hsq0)
    have hw : w = 0 := hz.symm.trans h2
    rw [hw, norm_zero, mul_zero]
    exact norm_nonneg _
  · have hCS := inner_sq_le_energy_mul_energy A hsymm henergy w z hzpos
    have hval : inner ℝ (A w) z = ‖w‖ ^ 2 := by
      rw [hsymm w z, hz, real_inner_self_eq_norm_sq]
    have hquartic : (‖w‖ ^ 2) ^ 2
        ≤ PositiveOperatorGap.energy A w * PositiveOperatorGap.energy A z := by
      rw [← hval]
      exact hCS
    have hEw : c * PositiveOperatorGap.energy A w ≤ ‖A w‖ ^ 2 := hlower w
    have hEz : c * PositiveOperatorGap.energy A z ≤ ‖w‖ ^ 2 := by
      have h := hlower z
      rwa [hz] at h
    have hprod : (c * PositiveOperatorGap.energy A w) *
        (c * PositiveOperatorGap.energy A z) ≤ ‖A w‖ ^ 2 * ‖w‖ ^ 2 :=
      mul_le_mul hEw hEz (mul_nonneg hc.le (henergy z)) (sq_nonneg _)
    rcases eq_or_lt_of_le (norm_nonneg w) with hw0 | hwpos
    · rw [← hw0, mul_zero]
      exact norm_nonneg _
    · -- `pow_pos` rather than `linarith [mul_pos hwpos hwpos]`: the latter
      -- leaves `linarith` to identify the monomial `‖w‖ * ‖w‖` with `‖w‖ ^ 2`,
      -- which is exactly the kind of step to keep syntactic.
      have hw2 : (0 : ℝ) < ‖w‖ ^ 2 := pow_pos hwpos 2
      -- The cancellation `c²‖w‖⁴ ≤ ‖Aw‖²‖w‖²  ⟹  c²‖w‖² ≤ ‖Aw‖²` is done by
      -- `le_of_mul_le_mul_right` against `hw2`, rather than left to `nlinarith`
      -- to discover as a product of the negated goal with `hw2`.
      have hchain : (c * ‖w‖) ^ 2 * ‖w‖ ^ 2 ≤ ‖A w‖ ^ 2 * ‖w‖ ^ 2 := by
        calc (c * ‖w‖) ^ 2 * ‖w‖ ^ 2 = c ^ 2 * (‖w‖ ^ 2) ^ 2 := by ring
          _ ≤ c ^ 2 * (PositiveOperatorGap.energy A w *
                PositiveOperatorGap.energy A z) :=
              mul_le_mul_of_nonneg_left hquartic (sq_nonneg c)
          _ = (c * PositiveOperatorGap.energy A w) *
                (c * PositiveOperatorGap.energy A z) := by ring
          _ ≤ ‖A w‖ ^ 2 * ‖w‖ ^ 2 := hprod
      have hsq : (c * ‖w‖) ^ 2 ≤ ‖A w‖ ^ 2 :=
        le_of_mul_le_mul_right hchain hw2
      exact (sq_le_sq₀ (mul_nonneg hc.le (norm_nonneg w))
        (norm_nonneg _)).mp hsq

/-- With a trivial kernel the spectral localization sharpens to
`spectrum ℝ A ⊆ [c, ∞)`: the isolated point `0` is not in the spectrum,
because `A` is invertible. -/
theorem spectrum_subset_Ici [CompleteSpace E]
    (A : E →L[ℝ] E) {c M : ℝ} (hc : 0 < c) (hM : 0 < M) (hcM : c ≤ M)
    (hsymm : ∀ y z : E, inner ℝ (A y) z = inner ℝ y (A z))
    (henergy : ∀ y : E, 0 ≤ PositiveOperatorGap.energy A y)
    (hlower : ∀ y : E, c * PositiveOperatorGap.energy A y ≤ ‖A y‖ ^ 2)
    (hformUpper : ∀ y : E, PositiveOperatorGap.energy A y ≤ M * ‖y‖ ^ 2)
    (hnormUpper : ∀ y : E, ‖A y‖ ^ 2 ≤ M * PositiveOperatorGap.energy A y)
    (hker : ∀ y : E, A y = 0 → y = 0) :
    spectrum ℝ A ⊆ Set.Ici c := by
  have hunit : IsUnit A :=
    isUnit_of_quadratic_gap A hc hM hcM hsymm henergy hlower hformUpper
      hnormUpper hker
  have hzero : (0 : ℝ) ∉ spectrum ℝ A := (spectrum.zero_notMem_iff ℝ).mpr hunit
  intro μ hμ
  rcases P13SpectralGap.spectrum_subset_zero_union_Ici A hc hsymm henergy
      hlower hμ with h0 | hge
  · rw [Set.mem_singleton_iff] at h0
    subst h0
    exact absurd hμ hzero
  · exact hge

end Abstract

section P13

variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The universal upper bound `M = 4·6 = 24` for the six-generator Laplacian
of the printed presentation, in the form the sharp bound consumes. -/
theorem p13_energy_le (rho : P13 →* (F ≃ₗᵢ[ℝ] F)) (y : F) :
    PositiveOperatorGap.energy (generatorLaplacianOperator p13Generator rho) y
      ≤ 24 * ‖y‖ ^ 2 :=
  le_trans (generatorLaplacian_energy_le p13Generator rho y)
    (by norm_num [Fintype.card_fin])

/-- The companion universal estimate `‖Δy‖² ≤ 24⟪y,Δy⟫`. -/
theorem p13_norm_sq_le (rho : P13 →* (F ≃ₗᵢ[ℝ] F)) (y : F) :
    ‖generatorLaplacianOperator p13Generator rho y‖ ^ 2
      ≤ 24 * PositiveOperatorGap.energy
          (generatorLaplacianOperator p13Generator rho) y :=
  le_trans (generatorLaplacian_norm_sq_le p13Generator rho y)
    (by norm_num [Fintype.card_fin])

/-- **The printed constant, as a displacement bound.**  In an orthogonal
representation of `P13` with no nonzero invariant vector, the six-generator
Kazhdan Laplacian satisfies `‖Δ x‖ ≥ (1/500) ‖x‖`.

This is the payload the manuscript's Step 1 spectral sentence carries, with
the printed constant `1/500` and no loss. -/
theorem p13_norm_lower_bound [CompleteSpace F]
    (rho : P13 →* (F ≃ₗᵢ[ℝ] F))
    (hno : ∀ x : F, (∀ g : P13, rho g x = x) → x = 0) (x : F) :
    (1 / 500 : ℝ) * ‖x‖
      ≤ ‖generatorLaplacianOperator p13Generator rho x‖ := by
  refine norm_lower_bound_of_quadratic_gap
    (generatorLaplacianOperator p13Generator rho)
    (c := (1 / 500 : ℝ)) (M := (24 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ x
  · intro y z
    exact generatorLaplacian_symmetric p13Generator rho y z
  · intro y
    rw [generatorLaplacian_energy p13Generator rho y]
    exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  · intro y
    exact p13_generatorLaplacian_quadratic_gap rho y
  · exact p13_energy_le rho
  · exact p13_norm_sq_le rho
  · intro y hy
    exact hno y (invariant_of_generatorLaplacian_eq_zero p13Generator
      closure_range_p13Generator rho y hy)

/-- **The sharpened spectral localization.**  In an orthogonal representation
of `P13` with no nonzero invariant vector, the spectrum of the six-generator
Kazhdan Laplacian lies in `[1/500, ∞)`: the isolated `0` of
`P13SpectralGap.t1_04_p13_spectrum_subset` is not attained. -/
theorem p13_spectrum_subset_Ici [CompleteSpace F]
    (rho : P13 →* (F ≃ₗᵢ[ℝ] F))
    (hno : ∀ x : F, (∀ g : P13, rho g x = x) → x = 0) :
    spectrum ℝ (generatorLaplacianOperator p13Generator rho)
      ⊆ Set.Ici (1 / 500 : ℝ) := by
  refine spectrum_subset_Ici (generatorLaplacianOperator p13Generator rho)
    (c := (1 / 500 : ℝ)) (M := (24 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_
  · intro y z
    exact generatorLaplacian_symmetric p13Generator rho y z
  · intro y
    rw [generatorLaplacian_energy p13Generator rho y]
    exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  · intro y
    exact p13_generatorLaplacian_quadratic_gap rho y
  · exact p13_energy_le rho
  · exact p13_norm_sq_le rho
  · intro y hy
    exact hno y (invariant_of_generatorLaplacian_eq_zero p13Generator
      closure_range_p13Generator rho y hy)

end P13

end P13SpectralGapNorm
end GroupApproximation
