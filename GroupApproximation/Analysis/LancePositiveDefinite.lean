import GroupApproximation.Analysis.LanceReiterMean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Sqrt

/-!
# Positive-definite functions, `ℓ²`-coefficients, and the Hulanicki step

## Where this sits in the Lance lane

`LanceReiterMean` proved the last arrow of Lance's direction — Reiter's
condition yields an invariant mean.  This module supplies the two arrows
above it, entirely at the level of finitely supported functions so that no
`ℓ²`-space instances are needed:

* **coefficients are positive definite**: for a finitely supported
  `ξ : G →₀ ℂ`, the matrix coefficient `g ↦ ⟪ξ, λ_g ξ⟫` of the left regular
  translation action is a positive-definite function on `G`
  (`isPositiveDefinite_coeffFn`);
* **the Hulanicki step**: unit vectors whose coefficients are close to `1`
  on a finite set are almost invariant in `ℓ²`
  (`l2NormSq_sub_lTrans`: `‖λ_g ξ - ξ‖² = 2 - 2 re ⟪ξ, λ_g ξ⟫`), and the
  squared modulus of an almost-invariant `ℓ²`-vector is an almost-invariant
  `ℓ¹`-density (`l1Norm_sqDensity_sub_le`, the Cauchy–Schwarz estimate
  `‖ |ξ|² ∘ λ_g − |ξ|² ‖₁ ≤ 2 ‖λ_g ξ − ξ‖₂`), which is Reiter's condition.

The two closing theorems are premise-free implications:

* `hasInvariantMean_of_almostInvariantVectors` — a group with almost
  invariant finitely supported `ℓ²`-vectors carries an invariant mean;
* `hasInvariantMean_of_coefficients_near_one` — the same with the almost
  invariance phrased through matrix coefficients, which is the interface
  the completely-positive compression of a CPAP produces.

## What is not claimed

Nothing here mentions `C*_λ(G)`, nuclearity, complete positivity or the
CPAP.  The arrow from the CPAP of the reduced algebra down to coefficients
near `1` — Stinespring compression along the canonical trace — is **not**
proved in this module or anywhere in the repository; `LanceReduction.lean`
states the exact residual.  Positive-definiteness of coefficients is proved
because it documents *why* the compression produces functions of this
shape, but the invariant-mean chain below consumes only the coefficient
bound, not positive-definiteness in the abstract.

## Manuscript status

Infrastructure for the `RE.05` row, which remains conditional on Lance
(`literature-input`).  No badge points here.
-/

namespace GroupApproximation
namespace LanceAmenability

open Finset

universe u

variable {G : Type u} [Group G]

/-! ## The inner product and the translation action, finitely supported -/

/-- The `ℓ²` inner product of two finitely supported complex functions,
conjugate-linear in the first argument, as Mathlib's inner products are. -/
def starInner (ξ η : G →₀ ℂ) : ℂ :=
  ξ.sum fun x c ↦ (starRingEnd ℂ) c * η x

omit [Group G] in
/-- The inner product as a sum over any finite set containing the support
of the first argument. -/
theorem starInner_eq_sum {ξ η : G →₀ ℂ} {s : Finset G}
    (hs : ξ.support ⊆ s) :
    starInner ξ η = ∑ x ∈ s, (starRingEnd ℂ) (ξ x) * η x := by
  show (∑ x ∈ ξ.support, (starRingEnd ℂ) (ξ x) * η x) = _
  refine Finset.sum_subset hs fun x _ hx ↦ ?_
  rw [Finsupp.notMem_support_iff.mp hx, map_zero, zero_mul]

/-- The left translation `(lTrans g ξ) x = ξ (g⁻¹ x)` of a finitely
supported complex function. -/
def lTrans (g : G) (ξ : G →₀ ℂ) : G →₀ ℂ :=
  Finsupp.equivMapDomain (Equiv.mulLeft g) ξ

@[simp] theorem lTrans_apply (g : G) (ξ : G →₀ ℂ) (x : G) :
    lTrans g ξ x = ξ (g⁻¹ * x) := by
  show ξ ((Equiv.mulLeft g).symm x) = ξ (g⁻¹ * x)
  rw [Equiv.mulLeft_symm_apply]

theorem lTrans_one (ξ : G →₀ ℂ) : lTrans 1 ξ = ξ := by
  ext x
  rw [lTrans_apply, inv_one, one_mul]

theorem lTrans_lTrans (a b : G) (ξ : G →₀ ℂ) :
    lTrans a (lTrans b ξ) = lTrans (a * b) ξ := by
  ext x
  rw [lTrans_apply, lTrans_apply, lTrans_apply, mul_inv_rev, mul_assoc]

/-! ## The squared `ℓ²` norm -/

/-- The squared `ℓ²` norm of a finitely supported complex function. -/
noncomputable def l2NormSq (ξ : G →₀ ℂ) : ℝ := ∑ x ∈ ξ.support, ‖ξ x‖ ^ 2

omit [Group G] in
/-- The squared norm as a sum over any finite set containing the
support. -/
theorem l2NormSq_eq_sum {ξ : G →₀ ℂ} {s : Finset G} (hs : ξ.support ⊆ s) :
    l2NormSq ξ = ∑ x ∈ s, ‖ξ x‖ ^ 2 := by
  refine Finset.sum_subset hs fun x _ hx ↦ ?_
  rw [Finsupp.notMem_support_iff.mp hx, norm_zero]
  norm_num

omit [Group G] in
theorem l2NormSq_nonneg (ξ : G →₀ ℂ) : 0 ≤ l2NormSq ξ :=
  Finset.sum_nonneg fun x _ ↦ by positivity

omit [Group G] in
/-- The inner product of a vector with itself is its squared norm. -/
theorem starInner_self (ξ : G →₀ ℂ) :
    starInner ξ ξ = (l2NormSq ξ : ℂ) := by
  show (∑ x ∈ ξ.support, (starRingEnd ℂ) (ξ x) * ξ x)
      = ((∑ x ∈ ξ.support, ‖ξ x‖ ^ 2 : ℝ) : ℂ)
  have h : ∀ x ∈ ξ.support,
      (starRingEnd ℂ) (ξ x) * ξ x = ((‖ξ x‖ ^ 2 : ℝ) : ℂ) := by
    intro x _
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [Finset.sum_congr rfl h]
  norm_cast

/-! ## Sesquilinearity -/

omit [Group G] in
theorem starInner_comm (ξ η : G →₀ ℂ) :
    starInner η ξ = (starRingEnd ℂ) (starInner ξ η) := by
  classical
  rw [starInner_eq_sum (s := ξ.support ∪ η.support) Finset.subset_union_right,
    starInner_eq_sum (s := ξ.support ∪ η.support) Finset.subset_union_left,
    map_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [map_mul, Complex.conj_conj, mul_comm]

omit [Group G] in
theorem starInner_sub_left (ξ ξ' η : G →₀ ℂ) :
    starInner (ξ - ξ') η = starInner ξ η - starInner ξ' η :=
  Finsupp.sum_sub_index fun a b₁ b₂ ↦ by rw [map_sub, sub_mul]

omit [Group G] in
theorem starInner_sub_right (ξ η η' : G →₀ ℂ) :
    starInner ξ (η - η') = starInner ξ η - starInner ξ η' := by
  show (∑ x ∈ ξ.support, (starRingEnd ℂ) (ξ x) * (η - η') x)
      = (∑ x ∈ ξ.support, (starRingEnd ℂ) (ξ x) * η x)
        - ∑ x ∈ ξ.support, (starRingEnd ℂ) (ξ x) * η' x
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Finsupp.sub_apply, mul_sub]

omit [Group G] in
theorem starInner_smul_left (c : ℂ) (ξ η : G →₀ ℂ) :
    starInner (c • ξ) η = (starRingEnd ℂ) c * starInner ξ η := by
  show (c • ξ).sum (fun x v ↦ (starRingEnd ℂ) v * η x)
      = (starRingEnd ℂ) c * ξ.sum (fun x v ↦ (starRingEnd ℂ) v * η x)
  rw [Finsupp.sum_smul_index' fun x ↦ by rw [map_zero, zero_mul]]
  have h1 : (ξ.sum fun a b ↦ (starRingEnd ℂ) (c • b) * η a)
      = ξ.sum fun a b ↦ (starRingEnd ℂ) c * ((starRingEnd ℂ) b * η a) := by
    show (∑ x ∈ ξ.support, (starRingEnd ℂ) (c • ξ x) * η x)
        = ∑ x ∈ ξ.support, (starRingEnd ℂ) c * ((starRingEnd ℂ) (ξ x) * η x)
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [smul_eq_mul, map_mul, mul_assoc]
  rw [h1, ← Finsupp.mul_sum]

omit [Group G] in
theorem starInner_smul_right (c : ℂ) (ξ η : G →₀ ℂ) :
    starInner ξ (c • η) = c * starInner ξ η := by
  show (∑ x ∈ ξ.support, (starRingEnd ℂ) (ξ x) * (c • η) x)
      = c * ∑ x ∈ ξ.support, (starRingEnd ℂ) (ξ x) * η x
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Finsupp.smul_apply, smul_eq_mul]
  ring

omit [Group G] in
theorem starInner_finsetSum_left {n : ℕ} (Θ : Fin n → (G →₀ ℂ))
    (η : G →₀ ℂ) :
    starInner (∑ i, Θ i) η = ∑ i, starInner (Θ i) η := by
  show (∑ i, Θ i).sum (fun x v ↦ (starRingEnd ℂ) v * η x)
      = ∑ i, (Θ i).sum (fun x v ↦ (starRingEnd ℂ) v * η x)
  rw [← Finsupp.sum_finsetSum_index (fun a ↦ by rw [map_zero, zero_mul])
    (fun a b₁ b₂ ↦ by rw [map_add, add_mul])]

omit [Group G] in
theorem starInner_finsetSum_right {n : ℕ} (ξ : G →₀ ℂ)
    (Θ : Fin n → (G →₀ ℂ)) :
    starInner ξ (∑ j, Θ j) = ∑ j, starInner ξ (Θ j) := by
  show (∑ x ∈ ξ.support, (starRingEnd ℂ) (ξ x) * (∑ j, Θ j) x)
      = ∑ j, starInner ξ (Θ j)
  calc (∑ x ∈ ξ.support, (starRingEnd ℂ) (ξ x) * (∑ j, Θ j) x)
      = ∑ x ∈ ξ.support, ∑ j, (starRingEnd ℂ) (ξ x) * Θ j x := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [Finsupp.finsetSum_apply, Finset.mul_sum]
    _ = ∑ j, ∑ x ∈ ξ.support, (starRingEnd ℂ) (ξ x) * Θ j x :=
        Finset.sum_comm
    _ = ∑ j, starInner ξ (Θ j) := rfl

/-! ## Unitarity of translation -/

/-- **Translation is unitary** for the finitely supported inner product. -/
theorem starInner_lTrans_lTrans (g : G) (ξ η : G →₀ ℂ) :
    starInner (lTrans g ξ) (lTrans g η) = starInner ξ η := by
  show (Finsupp.equivMapDomain (Equiv.mulLeft g) ξ).sum
      (fun x c ↦ (starRingEnd ℂ) c * (lTrans g η) x) = starInner ξ η
  rw [Finsupp.sum_equivMapDomain]
  simp only [Equiv.coe_mulLeft]
  show (∑ x ∈ ξ.support, (starRingEnd ℂ) (ξ x) * (lTrans g η) (g * x))
      = ∑ x ∈ ξ.support, (starRingEnd ℂ) (ξ x) * η x
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [lTrans_apply, inv_mul_cancel_left]

theorem l2NormSq_lTrans (g : G) (ξ : G →₀ ℂ) :
    l2NormSq (lTrans g ξ) = l2NormSq ξ := by
  have h1 := starInner_lTrans_lTrans g ξ ξ
  rw [starInner_self, starInner_self] at h1
  exact_mod_cast h1

/-! ## Matrix coefficients -/

/-- The matrix coefficient `g ↦ ⟪ξ, λ_g ξ⟫` of the translation action. -/
def coeffFn (ξ : G →₀ ℂ) : G → ℂ := fun g ↦ starInner ξ (lTrans g ξ)

theorem coeffFn_one (ξ : G →₀ ℂ) : coeffFn ξ 1 = (l2NormSq ξ : ℂ) := by
  show starInner ξ (lTrans 1 ξ) = _
  rw [lTrans_one, starInner_self]

/-- Inner products of translates are coefficients:
`⟪λ_s ξ, λ_t ξ⟫ = ⟪ξ, λ_{s⁻¹t} ξ⟫`. -/
theorem starInner_lTrans_pair (s t : G) (ξ : G →₀ ℂ) :
    starInner (lTrans s ξ) (lTrans t ξ) = coeffFn ξ (s⁻¹ * t) := by
  have h1 := starInner_lTrans_lTrans s ξ (lTrans (s⁻¹ * t) ξ)
  rw [lTrans_lTrans, mul_inv_cancel_left] at h1
  exact h1

/-! ## Positive-definite functions -/

/-- A function on a group is **positive definite** when every finite
Gram-type combination `∑ᵢⱼ c̄ᵢ cⱼ φ(sᵢ⁻¹ sⱼ)` is real and nonnegative. -/
def IsPositiveDefinite (φ : G → ℂ) : Prop :=
  ∀ (n : ℕ) (s : Fin n → G) (c : Fin n → ℂ),
    0 ≤ (∑ i, ∑ j,
        (starRingEnd ℂ) (c i) * c j * φ ((s i)⁻¹ * s j)).re ∧
      (∑ i, ∑ j,
        (starRingEnd ℂ) (c i) * c j * φ ((s i)⁻¹ * s j)).im = 0

/-- The value of a positive-definite function at the identity is real and
nonnegative. -/
theorem IsPositiveDefinite.one_nonneg {φ : G → ℂ}
    (h : IsPositiveDefinite φ) : 0 ≤ (φ 1).re ∧ (φ 1).im = 0 := by
  have h1 := h 1 (fun _ ↦ 1) (fun _ ↦ 1)
  simp only [Fin.sum_univ_one, map_one, one_mul, inv_one, mul_one] at h1
  exact h1

/-- **Matrix coefficients of the translation action are positive
definite.**  The Gram combination is the squared norm of
`Ξ = ∑ᵢ cᵢ λ_{sᵢ} ξ`. -/
theorem isPositiveDefinite_coeffFn (ξ : G →₀ ℂ) :
    IsPositiveDefinite (coeffFn ξ) := by
  intro n s c
  have hexp : starInner (∑ i, c i • lTrans (s i) ξ)
        (∑ i, c i • lTrans (s i) ξ)
      = ∑ i, ∑ j,
          (starRingEnd ℂ) (c i) * c j * coeffFn ξ ((s i)⁻¹ * s j) := by
    rw [starInner_finsetSum_left]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [starInner_smul_left, starInner_finsetSum_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [starInner_smul_right, starInner_lTrans_pair]
    ring
  have hself := starInner_self (∑ i, c i • lTrans (s i) ξ)
  rw [hexp] at hself
  refine ⟨?_, ?_⟩
  · rw [hself, Complex.ofReal_re]
    exact l2NormSq_nonneg _
  · rw [hself, Complex.ofReal_im]

/-! ## The Hulanicki step, `ℓ²` side: coefficients near `1` give almost
invariant vectors -/

/-- The parallelogram-type expansion of the squared norm of a
difference. -/
theorem l2NormSq_sub (a b : G →₀ ℂ) :
    l2NormSq (a - b) = l2NormSq a + l2NormSq b - 2 * (starInner b a).re := by
  have h1 : starInner (a - b) (a - b)
      = starInner a a - starInner a b - starInner b a + starInner b b := by
    rw [starInner_sub_left, starInner_sub_right, starInner_sub_right]
    ring
  have h2 := congrArg Complex.re h1
  rw [starInner_self, starInner_self, starInner_self] at h2
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re] at h2
  have h3 : (starInner b a).re = (starInner a b).re := by
    rw [starInner_comm a b, Complex.conj_re]
  linarith

/-- **The coefficient identity**: for a unit vector,
`‖λ_g ξ − ξ‖² = 2 − 2 re ⟪ξ, λ_g ξ⟫`. -/
theorem l2NormSq_sub_lTrans {ξ : G →₀ ℂ} (hξ : l2NormSq ξ = 1) (g : G) :
    l2NormSq (lTrans g ξ - ξ) = 2 - 2 * (coeffFn ξ g).re := by
  have h1 := l2NormSq_sub (lTrans g ξ) ξ
  rw [l2NormSq_lTrans, hξ] at h1
  have h2 : starInner ξ (lTrans g ξ) = coeffFn ξ g := rfl
  rw [h2] at h1
  linarith

/-! ## The Hulanicki step, `ℓ¹` side: `|ξ|²` is an almost invariant
density -/

/-- The squared-modulus density of an `ℓ²`-vector. -/
noncomputable def sqDensity (ξ : G →₀ ℂ) : G →₀ ℝ :=
  ξ.mapRange (fun c ↦ ‖c‖ ^ 2) (by simp)

omit [Group G] in
@[simp] theorem sqDensity_apply (ξ : G →₀ ℂ) (x : G) :
    sqDensity ξ x = ‖ξ x‖ ^ 2 :=
  Finsupp.mapRange_apply

omit [Group G] in
theorem sqDensity_nonneg (ξ : G →₀ ℂ) : ∀ x, 0 ≤ sqDensity ξ x := by
  intro x
  rw [sqDensity_apply]
  positivity

omit [Group G] in
theorem totalMass_sqDensity (ξ : G →₀ ℂ) :
    totalMass (sqDensity ξ) = l2NormSq ξ := by
  have hsub : (sqDensity ξ).support ⊆ ξ.support := Finsupp.support_mapRange
  have h1 : totalMass (sqDensity ξ) = ∑ x ∈ ξ.support, sqDensity ξ x :=
    Finset.sum_subset hsub fun x _ hx ↦ Finsupp.notMem_support_iff.mp hx
  rw [h1]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [sqDensity_apply]

theorem leftTranslate_sqDensity (g : G) (ξ : G →₀ ℂ) :
    leftTranslate g (sqDensity ξ) = sqDensity (lTrans g ξ) := by
  ext x
  rw [leftTranslate_apply, sqDensity_apply, sqDensity_apply, lTrans_apply]

/-- The pointwise square-difference estimate. -/
theorem abs_sq_sub_sq_le (a b : ℂ) :
    |‖a‖ ^ 2 - ‖b‖ ^ 2| ≤ (‖a‖ + ‖b‖) * ‖a - b‖ := by
  calc |‖a‖ ^ 2 - ‖b‖ ^ 2|
      = |(‖a‖ + ‖b‖) * (‖a‖ - ‖b‖)| := by rw [sq_sub_sq]
    _ = (‖a‖ + ‖b‖) * |‖a‖ - ‖b‖| := by
        rw [abs_mul,
          abs_of_nonneg (add_nonneg (norm_nonneg a) (norm_nonneg b))]
    _ ≤ (‖a‖ + ‖b‖) * ‖a - b‖ :=
        mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le a b)
          (add_nonneg (norm_nonneg a) (norm_nonneg b))

theorem add_sq_le_two_mul (p q : ℝ) : (p + q) ^ 2 ≤ 2 * p ^ 2 + 2 * q ^ 2 := by
  have h := two_mul_le_add_sq p q
  rw [add_sq]
  linarith

omit [Group G] in
/-- **The Cauchy–Schwarz `ℓ¹`-estimate**: for unit vectors `a` and `b`,
`‖ |a|² − |b|² ‖₁ ≤ 2 ‖a − b‖₂`. -/
theorem l1Norm_sqDensity_sub_le {a b : G →₀ ℂ}
    (ha : l2NormSq a = 1) (hb : l2NormSq b = 1) :
    l1Norm (sqDensity a - sqDensity b)
      ≤ 2 * Real.sqrt (l2NormSq (a - b)) := by
  classical
  have hsub : (sqDensity a - sqDensity b).support
      ⊆ a.support ∪ b.support :=
    (Finsupp.support_sub).trans
      (Finset.union_subset_union Finsupp.support_mapRange
        Finsupp.support_mapRange)
  have habsub : (a - b).support ⊆ a.support ∪ b.support :=
    Finsupp.support_sub
  have hSnn : (0 : ℝ) ≤ ∑ x ∈ a.support ∪ b.support,
      (‖a x‖ + ‖b x‖) * ‖a x - b x‖ :=
    Finset.sum_nonneg fun x _ ↦
      mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  -- step 1: the ℓ¹ norm is dominated by the cross sum
  have hstep1 : l1Norm (sqDensity a - sqDensity b)
      ≤ ∑ x ∈ a.support ∪ b.support, (‖a x‖ + ‖b x‖) * ‖a x - b x‖ := by
    have h1 : l1Norm (sqDensity a - sqDensity b)
        = ∑ x ∈ a.support ∪ b.support, |(sqDensity a - sqDensity b) x| := by
      refine Finset.sum_subset hsub fun x _ hx ↦ ?_
      rw [Finsupp.notMem_support_iff.mp hx, abs_zero]
    rw [h1]
    refine Finset.sum_le_sum fun x _ ↦ ?_
    rw [Finsupp.sub_apply, sqDensity_apply, sqDensity_apply]
    exact abs_sq_sub_sq_le (a x) (b x)
  -- step 2: Cauchy–Schwarz bounds the square of the cross sum
  have hsq : (∑ x ∈ a.support ∪ b.support, (‖a x‖ + ‖b x‖) ^ 2) ≤ 4 := by
    have h4 : (∑ x ∈ a.support ∪ b.support, (‖a x‖ + ‖b x‖) ^ 2)
        ≤ ∑ x ∈ a.support ∪ b.support,
            (2 * ‖a x‖ ^ 2 + 2 * ‖b x‖ ^ 2) :=
      Finset.sum_le_sum fun x _ ↦ add_sq_le_two_mul _ _
    have h5 : (∑ x ∈ a.support ∪ b.support,
          (2 * ‖a x‖ ^ 2 + 2 * ‖b x‖ ^ 2))
        = 2 * (∑ x ∈ a.support ∪ b.support, ‖a x‖ ^ 2)
          + 2 * ∑ x ∈ a.support ∪ b.support, ‖b x‖ ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h6 : (∑ x ∈ a.support ∪ b.support, ‖a x‖ ^ 2) = 1 := by
      have hsubl : a.support ⊆ a.support ∪ b.support :=
        Finset.subset_union_left
      rw [← l2NormSq_eq_sum hsubl]
      exact ha
    have h7 : (∑ x ∈ a.support ∪ b.support, ‖b x‖ ^ 2) = 1 := by
      have hsubr : b.support ⊆ a.support ∪ b.support :=
        Finset.subset_union_right
      rw [← l2NormSq_eq_sum hsubr]
      exact hb
    calc (∑ x ∈ a.support ∪ b.support, (‖a x‖ + ‖b x‖) ^ 2)
        ≤ ∑ x ∈ a.support ∪ b.support,
            (2 * ‖a x‖ ^ 2 + 2 * ‖b x‖ ^ 2) := h4
      _ = 2 * (∑ x ∈ a.support ∪ b.support, ‖a x‖ ^ 2)
          + 2 * ∑ x ∈ a.support ∪ b.support, ‖b x‖ ^ 2 := h5
      _ = 4 := by rw [h6, h7]; norm_num
  have hr : (∑ x ∈ a.support ∪ b.support, ‖a x - b x‖ ^ 2)
      = l2NormSq (a - b) := by
    have h8 : (∑ x ∈ a.support ∪ b.support, ‖a x - b x‖ ^ 2)
        = ∑ x ∈ a.support ∪ b.support, ‖(a - b) x‖ ^ 2 := by
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [Finsupp.sub_apply]
    rw [h8]
    exact (l2NormSq_eq_sum habsub).symm
  have hrnn : (0 : ℝ) ≤ ∑ x ∈ a.support ∪ b.support, ‖a x - b x‖ ^ 2 :=
    Finset.sum_nonneg fun x _ ↦ by positivity
  have hstep2 : (∑ x ∈ a.support ∪ b.support,
        (‖a x‖ + ‖b x‖) * ‖a x - b x‖) ^ 2 ≤ 4 * l2NormSq (a - b) := by
    calc (∑ x ∈ a.support ∪ b.support, (‖a x‖ + ‖b x‖) * ‖a x - b x‖) ^ 2
        ≤ (∑ x ∈ a.support ∪ b.support, (‖a x‖ + ‖b x‖) ^ 2)
            * ∑ x ∈ a.support ∪ b.support, ‖a x - b x‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ 4 * ∑ x ∈ a.support ∪ b.support, ‖a x - b x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hsq hrnn
      _ = 4 * l2NormSq (a - b) := by rw [hr]
  -- step 3: extract the square root
  have hstep3 : (∑ x ∈ a.support ∪ b.support,
        (‖a x‖ + ‖b x‖) * ‖a x - b x‖)
      ≤ 2 * Real.sqrt (l2NormSq (a - b)) := by
    have h9 := Real.sqrt_le_sqrt hstep2
    rw [Real.sqrt_sq hSnn] at h9
    have h11 : Real.sqrt (4 * l2NormSq (a - b))
        = 2 * Real.sqrt (l2NormSq (a - b)) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (sq_nonneg 2),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    rw [h11] at h9
    exact h9
  exact hstep1.trans hstep3

/-! ## The two premise-free closing implications -/

/-- **Almost invariant `ℓ²`-vectors give Reiter's condition.** -/
theorem reiterCondition_of_almostInvariantVectors
    (h : ∀ (F : Finset G) (ε : ℝ), 0 < ε →
      ∃ ξ : G →₀ ℂ, l2NormSq ξ = 1 ∧
        ∀ g ∈ F, l2NormSq (lTrans g ξ - ξ) ≤ ε) :
    ReiterCondition G := by
  intro F ε hε
  obtain ⟨ξ, hξ1, hξ2⟩ := h F ((ε / 2) ^ 2) (by positivity)
  refine ⟨sqDensity ξ, sqDensity_nonneg ξ, ?_, fun g hg ↦ ?_⟩
  · rw [totalMass_sqDensity, hξ1]
  · have ha : l2NormSq (lTrans g ξ) = 1 := by
      rw [l2NormSq_lTrans, hξ1]
    have hb := l1Norm_sqDensity_sub_le ha hξ1
    rw [← leftTranslate_sqDensity] at hb
    refine hb.trans ?_
    have h3 : Real.sqrt (l2NormSq (lTrans g ξ - ξ))
        ≤ Real.sqrt ((ε / 2) ^ 2) := Real.sqrt_le_sqrt (hξ2 g hg)
    rw [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ ε / 2)] at h3
    linarith

/-- **Almost invariant `ℓ²`-vectors give an invariant mean.** -/
theorem hasInvariantMean_of_almostInvariantVectors
    (h : ∀ (F : Finset G) (ε : ℝ), 0 < ε →
      ∃ ξ : G →₀ ℂ, l2NormSq ξ = 1 ∧
        ∀ g ∈ F, l2NormSq (lTrans g ξ - ξ) ≤ ε) :
    Amenability.HasInvariantMean G :=
  hasInvariantMean_of_reiter (reiterCondition_of_almostInvariantVectors h)

/-- **Coefficients near `1` give an invariant mean.**  This is the
interface the completely positive compression of a CPAP produces: unit
vectors whose translation coefficients are uniformly close to `1` on any
prescribed finite set. -/
theorem hasInvariantMean_of_coefficients_near_one
    (h : ∀ (F : Finset G) (ε : ℝ), 0 < ε →
      ∃ ξ : G →₀ ℂ, l2NormSq ξ = 1 ∧
        ∀ g ∈ F, 1 - ε ≤ (coeffFn ξ g).re) :
    Amenability.HasInvariantMean G := by
  refine hasInvariantMean_of_almostInvariantVectors fun F ε hε ↦ ?_
  obtain ⟨ξ, hξ1, hξ2⟩ := h F (ε / 2) (by positivity)
  refine ⟨ξ, hξ1, fun g hg ↦ ?_⟩
  rw [l2NormSq_sub_lTrans hξ1 g]
  have h2 := hξ2 g hg
  linarith

end LanceAmenability
end GroupApproximation
