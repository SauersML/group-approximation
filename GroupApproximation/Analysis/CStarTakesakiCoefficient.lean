import GroupApproximation.Analysis.CStarTensorProductSpatial

/-!
# The coefficient calculus for Takesaki's identification

## Where this sits

`CStarMinTensorNorm` defines the canonical minimal tensor norm as a supremum
over GNS pair representations, and records that **Takesaki's identification**
--- the spatial norm of any faithful pair equals the minimal norm --- is not
claimed.  This module is the first of the lane that closes the reachable half
of that gap.  It contains no states and no GNS: only the algebra of *matrix
coefficients* of a product representation, and two operator lemmas, all at
the generality of the spatial lane (inner product spaces, not necessarily
complete; `StarRep`s of complex ⋆-algebras, not necessarily C⋆).

## The three devices

1. **The slice maps.**  For a ⋆-representation `ρ` of `B` on `K` and finite
   families `a : Fin n → A`, `η : Fin n → K`, the *left slice*
   `leftSlice ρ a η : A ⊗[ℂ] B →ₗ[ℂ] A` sends `c ⊗ d` to
   `Σᵢⱼ ⟪ηᵢ, ρ(d) ηⱼ⟫ • (aᵢ⋆ c aⱼ)`.  Its two properties:

   * `leftSlice_star`: it intertwines the involutions, so it carries
     `x⋆ * x` to a selfadjoint element of `A`;
   * `inner_coeffVector_spatialHom`: for **every** ⋆-representation `π` of
     `A` on `H` and every `ζ : H`, the quadratic form of the product
     representation at `w_ζ = Σⱼ π(aⱼ)ζ ⊗ ηⱼ` computes on the slice:
     `⟪w_ζ, (π ⊗ ρ)(y) w_ζ⟫ = ⟪ζ, π(leftSlice ρ a η y) ζ⟫`.

   This is the linearization that drives the identification: a quadratic
   form of the tensor product, at an arbitrary finite vector, becomes the
   value of a *single element of `A`* under a vector functional of `π`.
   The mirrored `rightSlice` does the same on the second factor.

2. **The numerical-range bound** (`norm_smul_one_sub_le_of_isAdjoint`): a
   bounded operator that is its own adjoint and has nonnegative quadratic
   form satisfies `‖‖T‖•1 - T‖ ≤ ‖T‖`.  This is the spectrum-free,
   order-free surrogate for "`T ≥ 0`", proved by two applications of
   Cauchy--Schwarz.  No completeness, no C⋆-structure on the target, no
   functional calculus.

3. **The positivity transfer** (`re_apply_nonneg_of_norm_smul_one_sub_le`):
   a unital contraction `f : A →L[ℂ] ℂ` on a unital C⋆-algebra is
   nonnegative on any `r` with `‖‖r‖•1 - r‖ ≤ ‖r‖`.  Combined with (2) and
   the isometry of a faithful ⋆-homomorphism this transports operator
   positivity to *all* states at once --- the step for which the textbook
   route uses weak-⋆ density of vector states (Fell's theorem), here made
   unnecessary.

Also here: `opNorm_le_of_dense`, the operator-norm bound from a dense
submodule, used downstream to pass from coefficient vectors to all vectors.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  The identification
half itself is `CStarTakesakiMinLe.lean`; the exactness rows `SO.16` and
`RE.05` are untouched by this module.
-/

namespace GroupApproximation
namespace CStarTensor

open scoped InnerProductSpace TensorProduct

universe u v w x

/-! ## The operator norm from a dense submodule -/

/-- A pointwise bound on a dense submodule bounds the operator norm: the
bound set `{w | ‖T w‖ ≤ C * ‖w‖}` is closed. -/
theorem opNorm_le_of_dense {E : Type u} {F : Type v}
    [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (T : E →L[ℂ] F) {s : Submodule ℂ E} (hs : Dense (s : Set E)) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ w ∈ s, ‖T w‖ ≤ C * ‖w‖) : ‖T‖ ≤ C := by
  refine T.opNorm_le_bound hC fun w => ?_
  have hclosed : IsClosed {w : E | ‖T w‖ ≤ C * ‖w‖} :=
    isClosed_le (continuous_norm.comp T.continuous)
      (continuous_const.mul continuous_norm)
  have hsub : (s : Set E) ⊆ {w : E | ‖T w‖ ≤ C * ‖w‖} := fun w hw => h w hw
  have hall : closure (s : Set E) ⊆ {w : E | ‖T w‖ ≤ C * ‖w‖} :=
    closure_minimal hsub hclosed
  have hw : w ∈ closure (s : Set E) := by
    rw [hs.closure_eq]
    trivial
  exact hall hw

/-! ## Real-part bridges

`inner_self_eq_norm_sq` and `inner_self_im` are stated at `RCLike.re` and
`RCLike.im`; this lane works with the `Complex.re`/`Complex.im` projections.
The two bridges restate them once, so every rewrite below matches
syntactically. -/

theorem re_inner_self {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (v : V) : (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := by
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) v
  simpa [RCLike.re_to_complex] using h

theorem im_inner_self {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (v : V) : (⟪v, v⟫_ℂ).im = 0 := by
  have h := inner_self_im (𝕜 := ℂ) v
  simpa [RCLike.im_to_complex] using h

/-! ## The numerical-range bound -/

section Numerical

variable {V : Type w} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- For a bounded operator that is its own adjoint and has nonnegative
quadratic form, `‖T ζ‖² ≤ ‖T‖ * re ⟪ζ, T ζ⟫`: the operator Cauchy--Schwarz
inequality for the positive form `(u, v) ↦ ⟪u, T v⟫`, obtained without
polarization by testing positivity at the shifted vector
`ζ - ‖T‖⁻¹ • T ζ`. -/
theorem norm_apply_sq_le_of_isAdjoint {T : V →L[ℂ] V} (hT : IsAdjoint T T)
    (hpos : ∀ ζ : V, 0 ≤ (⟪ζ, T ζ⟫_ℂ).re) (ζ : V) :
    ‖T ζ‖ ^ 2 ≤ ‖T‖ * (⟪ζ, T ζ⟫_ℂ).re := by
  rcases eq_or_ne (T ζ) 0 with h0 | h0
  · have hβ : ‖T ζ‖ = 0 := by rw [h0, norm_zero]
    rw [hβ]
    have h1 := hpos ζ
    nlinarith [norm_nonneg T]
  · set t := ‖T‖ with ht_def
    set α := (⟪ζ, T ζ⟫_ℂ).re with hα_def
    have hβpos : 0 < ‖T ζ‖ := norm_pos_iff.mpr h0
    have hζ : ζ ≠ 0 := by
      intro h
      rw [h, map_zero] at h0
      exact h0 rfl
    have hζn : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
    have ht : 0 < t := by
      have h1 : 0 < t * ‖ζ‖ := lt_of_lt_of_le hβpos (T.le_opNorm ζ)
      nlinarith
    -- the third-order coefficient, by genuine Cauchy--Schwarz
    have hγ : (⟪T ζ, T (T ζ)⟫_ℂ).re ≤ t * ‖T ζ‖ ^ 2 := by
      have h2 : (⟪T ζ, T (T ζ)⟫_ℂ).re ≤ ‖⟪T ζ, T (T ζ)⟫_ℂ‖ :=
        Complex.re_le_norm _
      have h3 : ‖⟪T ζ, T (T ζ)⟫_ℂ‖ ≤ ‖T ζ‖ * ‖T (T ζ)‖ :=
        norm_inner_le_norm _ _
      have h4 : ‖T (T ζ)‖ ≤ t * ‖T ζ‖ := T.le_opNorm _
      nlinarith [norm_nonneg (T ζ)]
    -- the second-order coefficient is real, and is `‖T ζ‖²`
    have hTT : ⟪ζ, T (T ζ)⟫_ℂ = ⟪T ζ, T ζ⟫_ℂ := (hT ζ (T ζ)).symm
    have hTTre : (⟪ζ, T (T ζ)⟫_ℂ).re = ‖T ζ‖ ^ 2 := by
      rw [hTT]
      exact re_inner_self (T ζ)
    have hTTim : (⟪ζ, T (T ζ)⟫_ℂ).im = 0 := by
      rw [hTT]
      exact im_inner_self (T ζ)
    -- positivity at the shifted vector
    set c : ℂ := ((t⁻¹ : ℝ) : ℂ) with hc_def
    have hcre : c.re = t⁻¹ := by rw [hc_def, Complex.ofReal_re]
    have hcim : c.im = 0 := by rw [hc_def, Complex.ofReal_im]
    have h7 := hpos (ζ - c • T ζ)
    have e1 : T (ζ - c • T ζ) = T ζ - c • T (T ζ) := by
      rw [map_sub, map_smul]
    have e2 : ⟪ζ - c • T ζ, T (ζ - c • T ζ)⟫_ℂ
        = ⟪ζ, T ζ⟫_ℂ - c * ⟪ζ, T (T ζ)⟫_ℂ
          - ((starRingEnd ℂ) c * ⟪T ζ, T ζ⟫_ℂ
            - (starRingEnd ℂ) c * (c * ⟪T ζ, T (T ζ)⟫_ℂ)) := by
      rw [e1, inner_sub_left, inner_sub_right, inner_sub_right,
        inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right]
    have hβre : (⟪T ζ, T ζ⟫_ℂ).re = ‖T ζ‖ ^ 2 := re_inner_self (T ζ)
    have hβim : (⟪T ζ, T ζ⟫_ℂ).im = 0 := im_inner_self (T ζ)
    have hquad : 0 ≤ α - 2 * t⁻¹ * ‖T ζ‖ ^ 2
        + t⁻¹ ^ 2 * (⟪T ζ, T (T ζ)⟫_ℂ).re := by
      have h8 := h7
      rw [e2] at h8
      have h9 : (⟪ζ, T ζ⟫_ℂ - c * ⟪ζ, T (T ζ)⟫_ℂ
          - ((starRingEnd ℂ) c * ⟪T ζ, T ζ⟫_ℂ
            - (starRingEnd ℂ) c * (c * ⟪T ζ, T (T ζ)⟫_ℂ))).re
          = α - 2 * t⁻¹ * ‖T ζ‖ ^ 2
            + t⁻¹ ^ 2 * (⟪T ζ, T (T ζ)⟫_ℂ).re := by
        have hcc : (starRingEnd ℂ) c = c := by
          rw [hc_def, Complex.conj_ofReal]
        rw [hcc]
        simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, hcre,
          hcim, hTTre, hTTim, hβre, hβim, hα_def]
        ring
      rw [h9] at h8
      exact h8
    -- combine
    have h10 : t⁻¹ ^ 2 * (⟪T ζ, T (T ζ)⟫_ℂ).re
        ≤ t⁻¹ ^ 2 * (t * ‖T ζ‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hγ (sq_nonneg _)
    have h11 : t⁻¹ ^ 2 * (t * ‖T ζ‖ ^ 2) = t⁻¹ * ‖T ζ‖ ^ 2 := by
      field_simp
      ring
    have h12 : t⁻¹ * ‖T ζ‖ ^ 2 ≤ α := by nlinarith
    have h13 : t * (t⁻¹ * ‖T ζ‖ ^ 2) ≤ t * α :=
      mul_le_mul_of_nonneg_left h12 ht.le
    have h14 : t * (t⁻¹ * ‖T ζ‖ ^ 2) = ‖T ζ‖ ^ 2 := by
      rw [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
    rw [h14] at h13
    exact h13

/-- **The numerical-range bound.**  An operator that is its own adjoint and
has nonnegative quadratic form satisfies `‖‖T‖ • 1 - T‖ ≤ ‖T‖`.  This is
the spectrum-free surrogate for positivity. -/
theorem norm_smul_one_sub_le_of_isAdjoint {T : V →L[ℂ] V}
    (hT : IsAdjoint T T) (hpos : ∀ ζ : V, 0 ≤ (⟪ζ, T ζ⟫_ℂ).re) :
    ‖((‖T‖ : ℂ) • (1 : V →L[ℂ] V)) - T‖ ≤ ‖T‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun ζ => ?_
  set t := ‖T‖ with ht_def
  set α := (⟪ζ, T ζ⟫_ℂ).re with hα_def
  have hα0 : 0 ≤ α := hpos ζ
  have hkey : ‖T ζ‖ ^ 2 ≤ t * α := norm_apply_sq_le_of_isAdjoint hT hpos ζ
  have e3 : (((t : ℂ) • (1 : V →L[ℂ] V)) - T) ζ = (t : ℂ) • ζ - T ζ := by
    rw [sub_apply, smul_apply,
      one_apply_eq_self]
  have e4 : ‖(t : ℂ) • ζ - T ζ‖ ^ 2
      = t ^ 2 * ‖ζ‖ ^ 2 - 2 * t * α + ‖T ζ‖ ^ 2 := by
    have h1 : ‖(t : ℂ) • ζ - T ζ‖ ^ 2
        = (⟪(t : ℂ) • ζ - T ζ, (t : ℂ) • ζ - T ζ⟫_ℂ).re :=
      (re_inner_self _).symm
    have h2 : ⟪(t : ℂ) • ζ - T ζ, (t : ℂ) • ζ - T ζ⟫_ℂ
        = (starRingEnd ℂ) ((t : ℝ) : ℂ) * ((t : ℂ) * ⟪ζ, ζ⟫_ℂ)
          - (starRingEnd ℂ) ((t : ℝ) : ℂ) * ⟪ζ, T ζ⟫_ℂ
          - ((t : ℂ) * ⟪T ζ, ζ⟫_ℂ - ⟪T ζ, T ζ⟫_ℂ) := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right,
        inner_smul_left, inner_smul_left, inner_smul_right,
        inner_smul_right]
    have hconj : (starRingEnd ℂ) ((t : ℝ) : ℂ) = ((t : ℝ) : ℂ) :=
      Complex.conj_ofReal _
    have hζζre : (⟪ζ, ζ⟫_ℂ).re = ‖ζ‖ ^ 2 := re_inner_self ζ
    have hζζim : (⟪ζ, ζ⟫_ℂ).im = 0 := im_inner_self ζ
    have hTre : ⟪T ζ, ζ⟫_ℂ = (starRingEnd ℂ) ⟪ζ, T ζ⟫_ℂ :=
      (inner_conj_symm (T ζ) ζ).symm
    have hTTre2 : (⟪T ζ, T ζ⟫_ℂ).re = ‖T ζ‖ ^ 2 :=
      re_inner_self (T ζ)
    rw [h1, h2, hconj, hTre]
    simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im, hζζre, hζζim, hTTre2, hα_def]
    ring
  have e5 : ‖(t : ℂ) • ζ - T ζ‖ ^ 2 ≤ (t * ‖ζ‖) ^ 2 := by
    rw [e4]
    nlinarith [mul_nonneg (norm_nonneg T) hα0]
  have e6 : ‖(t : ℂ) • ζ - T ζ‖ ≤ t * ‖ζ‖ := by
    have hnn : 0 ≤ ‖(t : ℂ) • ζ - T ζ‖ := norm_nonneg _
    have hnn2 : 0 ≤ t * ‖ζ‖ := mul_nonneg (norm_nonneg T) (norm_nonneg ζ)
    exact (sq_le_sq₀ hnn hnn2).mp e5
  rw [e3]
  exact e6

end Numerical

/-! ## The positivity transfer to states -/

/-- **A unital contraction is nonnegative on any element within norm-reach
of a positive multiple of the identity.**  For `f 1 = 1`, `‖f‖ ≤ 1` and
`‖‖r‖•1 - r‖ ≤ ‖r‖`:  `0 ≤ re (f r)`. -/
theorem re_apply_nonneg_of_norm_smul_one_sub_le {A : Type u} [CStarAlgebra A]
    (f : A →L[ℂ] ℂ) (hf1 : f 1 = 1) (hf : ‖f‖ ≤ 1) {r : A}
    (hr : ‖((‖r‖ : ℂ) • (1 : A)) - r‖ ≤ ‖r‖) : 0 ≤ (f r).re := by
  have h1 : f r = ((‖r‖ : ℝ) : ℂ) - f (((‖r‖ : ℂ) • (1 : A)) - r) := by
    rw [map_sub, map_smul, hf1, smul_eq_mul, mul_one]
    ring
  have h2 : ‖f (((‖r‖ : ℂ) • (1 : A)) - r)‖ ≤ ‖r‖ := by
    have h3 := f.le_opNorm (((‖r‖ : ℂ) • (1 : A)) - r)
    have h4 : ‖f‖ * ‖((‖r‖ : ℂ) • (1 : A)) - r‖ ≤ 1 * ‖r‖ :=
      mul_le_mul hf hr (norm_nonneg _) zero_le_one
    rw [one_mul] at h4
    exact h3.trans h4
  have h5 : (f (((‖r‖ : ℂ) • (1 : A)) - r)).re ≤ ‖r‖ :=
    (Complex.re_le_norm _).trans h2
  rw [h1, Complex.sub_re, Complex.ofReal_re]
  linarith

/-! ## The slice maps -/

section Slice

variable {A : Type u} {B : Type v} [Ring A] [StarRing A] [Algebra ℂ A]
  [StarModule ℂ A] [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
variable {H : Type w} {K : Type x} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Slicing the second factor of the algebraic tensor product by a linear
functional: `c ⊗ d ↦ g d • c`.  The mirror of the spatial lane's
`sliceRight`. -/
noncomputable def sliceSecond (g : B →ₗ[ℂ] ℂ) : (A ⊗[ℂ] B) →ₗ[ℂ] A :=
  (TensorProduct.rid ℂ A).toLinearMap ∘ₗ TensorProduct.map LinearMap.id g

omit [StarRing A] [StarModule ℂ A] [StarRing B] [StarModule ℂ B] in
@[simp] theorem sliceSecond_tmul (g : B →ₗ[ℂ] ℂ) (c : A) (d : B) :
    sliceSecond g (c ⊗ₜ[ℂ] d) = g d • c := by
  simp only [sliceSecond]
  rw [LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, LinearEquiv.coe_toLinearMap, TensorProduct.rid_tmul]

variable {n : ℕ}

/-- **The left slice** of the coefficient pairing: for a ⋆-representation
`ρ` of `B` on `K` and families `a : Fin n → A`, `η : Fin n → K`, the linear
map `A ⊗[ℂ] B →ₗ[ℂ] A` with
`c ⊗ d ↦ Σᵢⱼ ⟪ηᵢ, ρ(d) ηⱼ⟫ • (star aᵢ * c * aⱼ)`. -/
noncomputable def leftSlice (ρ : StarRep B K) (a : Fin n → A)
    (η : Fin n → K) : (A ⊗[ℂ] B) →ₗ[ℂ] A :=
  ∑ i : Fin n, ∑ j : Fin n,
    (LinearMap.mulLeftRight ℂ (star (a i), a j)) ∘ₗ
      sliceSecond (vecFunctional ρ (η j) (η i))

theorem leftSlice_tmul (ρ : StarRep B K) (a : Fin n → A) (η : Fin n → K)
    (c : A) (d : B) :
    leftSlice ρ a η (c ⊗ₜ[ℂ] d)
      = ∑ i : Fin n, ∑ j : Fin n,
          ⟪η i, ρ.hom d (η j)⟫_ℂ • (star (a i) * c * a j) := by
  simp only [leftSlice]
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.comp_apply, sliceSecond_tmul, vecFunctional_apply, map_smul,
    LinearMap.mulLeftRight_apply]

/-- **The left slice intertwines the involutions.**  In particular it sends
`star x * x` to a selfadjoint element. -/
theorem leftSlice_star (ρ : StarRep B K) (a : Fin n → A) (η : Fin n → K)
    (y : A ⊗[ℂ] B) :
    leftSlice ρ a η (star y) = star (leftSlice ρ a η y) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [star_zero, map_zero, star_zero]
  | tmul c d =>
      rw [TensorProduct.star_tmul, leftSlice_tmul, leftSlice_tmul]
      have hterm : ∀ i j : Fin n,
          star (⟪η i, ρ.hom d (η j)⟫_ℂ • (star (a i) * c * a j))
            = ⟪η j, ρ.hom (star d) (η i)⟫_ℂ
                • (star (a j) * star c * a i) := by
        intro i j
        rw [star_smul]
        have h1 : star ⟪η i, ρ.hom d (η j)⟫_ℂ
            = ⟪η j, ρ.hom (star d) (η i)⟫_ℂ := by
          have h2 : (starRingEnd ℂ) ⟪η i, ρ.hom d (η j)⟫_ℂ
              = ⟪ρ.hom d (η j), η i⟫_ℂ :=
            inner_conj_symm (ρ.hom d (η j)) (η i)
          have h3 : ⟪ρ.hom d (η j), η i⟫_ℂ
              = ⟪η j, ρ.hom (star d) (η i)⟫_ℂ :=
            ρ.isAdjoint_star d (η j) (η i)
          calc star ⟪η i, ρ.hom d (η j)⟫_ℂ
              = (starRingEnd ℂ) ⟪η i, ρ.hom d (η j)⟫_ℂ := by
                rw [Complex.star_def]
            _ = ⟪ρ.hom d (η j), η i⟫_ℂ := h2
            _ = ⟪η j, ρ.hom (star d) (η i)⟫_ℂ := h3
        have h4 : star (star (a i) * c * a j)
            = star (a j) * star c * a i := by
          rw [star_mul, star_mul, star_star, mul_assoc]
        rw [h1, h4]
      have hR : star (∑ i : Fin n, ∑ j : Fin n,
            ⟪η i, ρ.hom d (η j)⟫_ℂ • (star (a i) * c * a j))
          = ∑ i : Fin n, ∑ j : Fin n,
              ⟪η j, ρ.hom (star d) (η i)⟫_ℂ
                • (star (a j) * star c * a i) := by
        rw [star_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [star_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact hterm i j
      rw [hR]
      exact Finset.sum_comm.symm
  | add y z hy hz => rw [star_add, map_add, map_add, hy, hz, star_add]

/-- The coefficient vector `Σⱼ π(aⱼ)ζ ⊗ ηⱼ` attached to a family of algebra
elements and a family of second-leg vectors. -/
noncomputable def coeffVector (π : StarRep A H) (ζ : H) (a : Fin n → A)
    (η : Fin n → K) : H ⊗[ℂ] K :=
  ∑ j : Fin n, (π.hom (a j) ζ) ⊗ₜ[ℂ] (η j)

/-- **The coefficient identity**: for every ⋆-representation `π` of `A`, the
quadratic form of the product representation at the coefficient vector
computes on the left slice, as a vector functional of `π` at the single
element `leftSlice ρ a η y ∈ A`. -/
theorem inner_coeffVector_spatialHom (π : StarRep A H) (ρ : StarRep B K)
    (a : Fin n → A) (η : Fin n → K) (ζ : H) (y : A ⊗[ℂ] B) :
    ⟪coeffVector π ζ a η, spatialHom π ρ y (coeffVector π ζ a η)⟫_ℂ
      = ⟪ζ, π.hom (leftSlice ρ a η y) ζ⟫_ℂ := by
  induction y using TensorProduct.induction_on with
  | zero =>
      simp only [map_zero, zero_apply, inner_zero_right]
  | tmul c d =>
      rw [spatialHom_tmul, leftSlice_tmul]
      simp only [coeffVector]
      -- normalize the left side to a double sum of products
      rw [map_sum, sum_inner]
      simp only [TensorProduct.mapL_tmul, inner_sum, TensorProduct.inner_tmul]
      -- normalize the right side to a double sum
      simp only [map_sum, map_smul, sum_apply,
        smul_apply, inner_sum, inner_smul_right]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      have hb : ⟪π.hom (a i) ζ, π.hom c (π.hom (a j) ζ)⟫_ℂ
          = ⟪ζ, π.hom (star (a i) * c * a j) ζ⟫_ℂ := by
        have h1 : ⟪π.hom (a i) ζ, π.hom c (π.hom (a j) ζ)⟫_ℂ
            = ⟪ζ, π.hom (star (a i)) (π.hom c (π.hom (a j) ζ))⟫_ℂ :=
          π.isAdjoint_star (a i) ζ (π.hom c (π.hom (a j) ζ))
        have h2 : π.hom (star (a i) * c * a j) ζ
            = π.hom (star (a i)) (π.hom c (π.hom (a j) ζ)) := by
          rw [map_mul, map_mul, mul_eq_comp, mul_eq_comp,
            ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
        rw [h1, h2]
      rw [hb]
      ring
  | add y z hy hz =>
      simp only [map_add, add_apply, inner_add_right,
        hy, hz]

/-- The coefficient identity at `y = 1`: the norm of the coefficient vector
computes on the left slice of the identity. -/
theorem inner_coeffVector_self (π : StarRep A H) (ρ : StarRep B K)
    (a : Fin n → A) (η : Fin n → K) (ζ : H) :
    ⟪coeffVector π ζ a η, coeffVector π ζ a η⟫_ℂ
      = ⟪ζ, π.hom (leftSlice ρ a η (1 : A ⊗[ℂ] B)) ζ⟫_ℂ := by
  have h := inner_coeffVector_spatialHom π ρ a η ζ (1 : A ⊗[ℂ] B)
  rw [map_one, one_apply_eq_self] at h
  exact h

/-! ## The mirrored slices, for the second factor -/

/-- **The right slice**: for a ⋆-representation `π` of `A` on `H` and
families `b : Fin n → B`, `ξ : Fin n → H`, the linear map
`A ⊗[ℂ] B →ₗ[ℂ] B` with
`c ⊗ d ↦ Σᵢⱼ ⟪ξᵢ, π(c) ξⱼ⟫ • (star bᵢ * d * bⱼ)`.  Built from the spatial
lane's `sliceRight`, which kills the first factor. -/
noncomputable def rightSlice (π : StarRep A H) (b : Fin n → B)
    (ξ : Fin n → H) : (A ⊗[ℂ] B) →ₗ[ℂ] B :=
  ∑ i : Fin n, ∑ j : Fin n,
    (LinearMap.mulLeftRight ℂ (star (b i), b j)) ∘ₗ
      sliceRight (vecFunctional π (ξ j) (ξ i))

omit [StarModule ℂ A] [StarModule ℂ B] in
theorem rightSlice_tmul (π : StarRep A H) (b : Fin n → B) (ξ : Fin n → H)
    (c : A) (d : B) :
    rightSlice π b ξ (c ⊗ₜ[ℂ] d)
      = ∑ i : Fin n, ∑ j : Fin n,
          ⟪ξ i, π.hom c (ξ j)⟫_ℂ • (star (b i) * d * b j) := by
  simp only [rightSlice]
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.comp_apply, sliceRight_tmul, vecFunctional_apply, map_smul,
    LinearMap.mulLeftRight_apply]

/-- The right slice intertwines the involutions. -/
theorem rightSlice_star (π : StarRep A H) (b : Fin n → B) (ξ : Fin n → H)
    (y : A ⊗[ℂ] B) :
    rightSlice π b ξ (star y) = star (rightSlice π b ξ y) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [star_zero, map_zero, star_zero]
  | tmul c d =>
      rw [TensorProduct.star_tmul, rightSlice_tmul, rightSlice_tmul]
      have hterm : ∀ i j : Fin n,
          star (⟪ξ i, π.hom c (ξ j)⟫_ℂ • (star (b i) * d * b j))
            = ⟪ξ j, π.hom (star c) (ξ i)⟫_ℂ
                • (star (b j) * star d * b i) := by
        intro i j
        rw [star_smul]
        have h1 : star ⟪ξ i, π.hom c (ξ j)⟫_ℂ
            = ⟪ξ j, π.hom (star c) (ξ i)⟫_ℂ := by
          have h2 : (starRingEnd ℂ) ⟪ξ i, π.hom c (ξ j)⟫_ℂ
              = ⟪π.hom c (ξ j), ξ i⟫_ℂ :=
            inner_conj_symm (π.hom c (ξ j)) (ξ i)
          have h3 : ⟪π.hom c (ξ j), ξ i⟫_ℂ
              = ⟪ξ j, π.hom (star c) (ξ i)⟫_ℂ :=
            π.isAdjoint_star c (ξ j) (ξ i)
          calc star ⟪ξ i, π.hom c (ξ j)⟫_ℂ
              = (starRingEnd ℂ) ⟪ξ i, π.hom c (ξ j)⟫_ℂ := by
                rw [Complex.star_def]
            _ = ⟪π.hom c (ξ j), ξ i⟫_ℂ := h2
            _ = ⟪ξ j, π.hom (star c) (ξ i)⟫_ℂ := h3
        have h4 : star (star (b i) * d * b j)
            = star (b j) * star d * b i := by
          rw [star_mul, star_mul, star_star, mul_assoc]
        rw [h1, h4]
      have hR : star (∑ i : Fin n, ∑ j : Fin n,
            ⟪ξ i, π.hom c (ξ j)⟫_ℂ • (star (b i) * d * b j))
          = ∑ i : Fin n, ∑ j : Fin n,
              ⟪ξ j, π.hom (star c) (ξ i)⟫_ℂ
                • (star (b j) * star d * b i) := by
        rw [star_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [star_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact hterm i j
      rw [hR]
      exact Finset.sum_comm.symm
  | add y z hy hz => rw [star_add, map_add, map_add, hy, hz, star_add]

/-- The mirrored coefficient vector `Σⱼ ξⱼ ⊗ ρ(bⱼ)ζ`. -/
noncomputable def rightCoeffVector (ρ : StarRep B K) (ζ : K)
    (b : Fin n → B) (ξ : Fin n → H) : H ⊗[ℂ] K :=
  ∑ j : Fin n, (ξ j) ⊗ₜ[ℂ] (ρ.hom (b j) ζ)

/-- **The mirrored coefficient identity**: the quadratic form at the
mirrored coefficient vector computes on the right slice, as a vector
functional of `ρ` at the single element `rightSlice π b ξ y ∈ B`. -/
theorem inner_rightCoeffVector_spatialHom (π : StarRep A H)
    (ρ : StarRep B K) (b : Fin n → B) (ξ : Fin n → H) (ζ : K)
    (y : A ⊗[ℂ] B) :
    ⟪rightCoeffVector ρ ζ b ξ, spatialHom π ρ y (rightCoeffVector ρ ζ b ξ)⟫_ℂ
      = ⟪ζ, ρ.hom (rightSlice π b ξ y) ζ⟫_ℂ := by
  induction y using TensorProduct.induction_on with
  | zero =>
      simp only [map_zero, zero_apply, inner_zero_right]
  | tmul c d =>
      rw [spatialHom_tmul, rightSlice_tmul]
      simp only [rightCoeffVector]
      rw [map_sum, sum_inner]
      simp only [TensorProduct.mapL_tmul, inner_sum, TensorProduct.inner_tmul]
      simp only [map_sum, map_smul, sum_apply,
        smul_apply, inner_sum, inner_smul_right]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      have hb : ⟪ρ.hom (b i) ζ, ρ.hom d (ρ.hom (b j) ζ)⟫_ℂ
          = ⟪ζ, ρ.hom (star (b i) * d * b j) ζ⟫_ℂ := by
        have h1 : ⟪ρ.hom (b i) ζ, ρ.hom d (ρ.hom (b j) ζ)⟫_ℂ
            = ⟪ζ, ρ.hom (star (b i)) (ρ.hom d (ρ.hom (b j) ζ))⟫_ℂ :=
          ρ.isAdjoint_star (b i) ζ (ρ.hom d (ρ.hom (b j) ζ))
        have h2 : ρ.hom (star (b i) * d * b j) ζ
            = ρ.hom (star (b i)) (ρ.hom d (ρ.hom (b j) ζ)) := by
          rw [map_mul, map_mul, mul_eq_comp, mul_eq_comp,
            ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
        rw [h1, h2]
      rw [hb]
  | add y z hy hz =>
      simp only [map_add, add_apply, inner_add_right,
        hy, hz]

/-- The mirrored identity at `y = 1`. -/
theorem inner_rightCoeffVector_self (π : StarRep A H) (ρ : StarRep B K)
    (b : Fin n → B) (ξ : Fin n → H) (ζ : K) :
    ⟪rightCoeffVector ρ ζ b ξ, rightCoeffVector ρ ζ b ξ⟫_ℂ
      = ⟪ζ, ρ.hom (rightSlice π b ξ (1 : A ⊗[ℂ] B)) ζ⟫_ℂ := by
  have h := inner_rightCoeffVector_spatialHom π ρ b ξ ζ (1 : A ⊗[ℂ] B)
  rw [map_one, one_apply_eq_self] at h
  exact h

end Slice

end CStarTensor
end GroupApproximation
