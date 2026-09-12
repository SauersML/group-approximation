import GroupApproximation.Analysis.LancePositiveDefinite
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Complex.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Almost invariant vectors from a positive-definite matrix kernel

This module is the finite algebra behind "the maximal group C⋆-algebra of a
nonamenable group is not nuclear" (`Analysis/LanceMaximalNuclear`).

## The input

* a matrix-valued function `D : G → Matrix Y Y ℂ` that is positive on pairs
  (`PairPositive`): for every `g` the `2 × 2` block form assembled from
  `D 1`, `D g`, `D g⁻¹` is nonnegative.  A completely positive map `down` into
  `M_Y(ℂ)` gives such a `D` by `D g = down (u_g)`, from the positive matrix
  `[u_{a_i}⋆ u_{a_j}]` with `a = (1, g)`;
* a finite family `d : ι → Y → (G →₀ ℂ)` of finitely supported vectors.

## The output

The correlation `corr D d g = ∑ₗ ∑_{y,y'} D g y y' ⟪d l y, λ_g (d l y')⟫` and the
**Reiter vector** `reiter D d`, the finitely supported function
`x ↦ √(∑ₗ ⟨v_l(x), D(1) v_l(x)⟩)` with `v_l(x) = (d l y x)_y`, satisfy

* `‖reiter D d‖² = Re corr D d 1`;
* `‖λ_g (reiter D d) - reiter D d‖² ≤ 2 Re corr 1 - Re corr g - Re corr g⁻¹`.

The second inequality is pointwise: at each `x` the cross term is at most
`2 √(mass(g⁻¹x)) √(mass x)`, by pair positivity at every scale `t` and the
optimal choice of `t`; so `(√mass(g⁻¹x) - √mass x)²` is at most the diagonal
terms minus the cross term, and the sums of the three pieces over `x` are the
three correlations.  So correlations near `1` give almost invariant unit
vectors (`exists_almostInvariant_of_corr`), hence an invariant mean.

## Manuscript status

Infrastructure for the sentence "here `C^*_{\max}(W)` is not nuclear, since `W`
is not amenable" (`non_mf_groups_exist.tex`, introduction).  Certifies no
manuscript step on its own.
-/

namespace GroupApproximation
namespace LanceMaximal

open LanceAmenability

universe u

/-! ## Two real inequalities -/

/-- If `R ≤ t² B + A / t²` for every `t > 0`, then `R ≤ 2 √A √B`: the infimum of
the right side over `t` is attained at `t² = √A / √B`, and it is `≤ 0` in the
degenerate cases. -/
theorem le_two_mul_sqrt_mul_sqrt {R A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 < t → R ≤ t ^ 2 * B + A / t ^ 2) :
    R ≤ 2 * Real.sqrt A * Real.sqrt B := by
  rcases hA.eq_or_lt with hA0 | hApos
  · subst hA0
    rw [Real.sqrt_zero, mul_zero, zero_mul]
    by_contra hR
    rw [not_le] at hR
    have hden : 0 < 2 * (B + 1) := by positivity
    have hden' : 2 * (B + 1) ≠ 0 := hden.ne'
    have hq : 0 < R / (2 * (B + 1)) := div_pos hR hden
    have htpos : 0 < Real.sqrt (R / (2 * (B + 1))) := Real.sqrt_pos.mpr hq
    have ht2 : Real.sqrt (R / (2 * (B + 1))) ^ 2 = R / (2 * (B + 1)) :=
      Real.sq_sqrt hq.le
    have hkey : Real.sqrt (R / (2 * (B + 1))) ^ 2 * (2 * (B + 1)) = R := by
      rw [ht2, div_mul_cancel₀ R hden']
    have hh := h _ htpos
    rw [zero_div, add_zero] at hh
    nlinarith [mul_pos (pow_pos htpos 2) (by linarith : (0 : ℝ) < B + 2)]
  · rcases hB.eq_or_lt with hB0 | hBpos
    · subst hB0
      rw [Real.sqrt_zero, mul_zero]
      by_contra hR
      rw [not_le] at hR
      have hR' : R ≠ 0 := hR.ne'
      have hnum : 0 < 2 * (A + 1) / R := div_pos (by positivity) hR
      have htpos : 0 < Real.sqrt (2 * (A + 1) / R) := Real.sqrt_pos.mpr hnum
      have ht2 : Real.sqrt (2 * (A + 1) / R) ^ 2 = 2 * (A + 1) / R :=
        Real.sq_sqrt hnum.le
      have hkey : Real.sqrt (2 * (A + 1) / R) ^ 2 * R = 2 * (A + 1) := by
        rw [ht2, div_mul_cancel₀ _ hR']
      have ht2pos : 0 < Real.sqrt (2 * (A + 1) / R) ^ 2 := pow_pos htpos 2
      have hdiv : A / Real.sqrt (2 * (A + 1) / R) ^ 2 *
          Real.sqrt (2 * (A + 1) / R) ^ 2 = A :=
        div_mul_cancel₀ A ht2pos.ne'
      have hh := h _ htpos
      rw [mul_zero, zero_add] at hh
      have hmul := mul_le_mul_of_nonneg_right hh ht2pos.le
      rw [hdiv] at hmul
      nlinarith
    · have hp : 0 < Real.sqrt A := Real.sqrt_pos.mpr hApos
      have hq : 0 < Real.sqrt B := Real.sqrt_pos.mpr hBpos
      have hp0 : Real.sqrt A ≠ 0 := hp.ne'
      have hq0 : Real.sqrt B ≠ 0 := hq.ne'
      have hAA : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA
      have hBB : Real.sqrt B * Real.sqrt B = B := Real.mul_self_sqrt hB
      have hpq : 0 < Real.sqrt A / Real.sqrt B := div_pos hp hq
      have htpos : 0 < Real.sqrt (Real.sqrt A / Real.sqrt B) := Real.sqrt_pos.mpr hpq
      have ht2 : Real.sqrt (Real.sqrt A / Real.sqrt B) ^ 2 = Real.sqrt A / Real.sqrt B :=
        Real.sq_sqrt hpq.le
      have hh := h _ htpos
      have e1 : Real.sqrt A / Real.sqrt B * B = Real.sqrt A * Real.sqrt B := by
        calc Real.sqrt A / Real.sqrt B * B
            = Real.sqrt A / Real.sqrt B * (Real.sqrt B * Real.sqrt B) := by rw [hBB]
          _ = Real.sqrt A * Real.sqrt B := by rw [← mul_assoc, div_mul_cancel₀ _ hq0]
      have e2 : A / (Real.sqrt A / Real.sqrt B) = Real.sqrt A * Real.sqrt B := by
        calc A / (Real.sqrt A / Real.sqrt B)
            = Real.sqrt A * Real.sqrt A * Real.sqrt B / Real.sqrt A := by
              rw [div_div_eq_mul_div, hAA]
          _ = Real.sqrt A * Real.sqrt B := by
              rw [mul_assoc, mul_div_cancel_left₀ _ hp0]
      rw [ht2, e1, e2] at hh
      linarith

/-- The squared difference of two square roots, bounded by the diagonal terms
minus any real number below twice their product. -/
theorem sqrt_sub_sqrt_sq_le {A B R : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hR : R ≤ 2 * Real.sqrt A * Real.sqrt B) :
    (Real.sqrt A - Real.sqrt B) ^ 2 ≤ A + B - R := by
  have h1 := Real.sq_sqrt hA
  have h2 := Real.sq_sqrt hB
  nlinarith [h1, h2, hR]

variable {G : Type u} [Group G]

/-! ## Translation facts for finitely supported vectors -/

theorem starInner_lTrans_left (g : G) (ξ η : G →₀ ℂ) :
    starInner (lTrans g ξ) η = starInner ξ (lTrans g⁻¹ η) := by
  have h := starInner_lTrans_lTrans g⁻¹ (lTrans g ξ) η
  rw [lTrans_lTrans, inv_mul_cancel, lTrans_one] at h
  exact h.symm

omit [Group G] in
theorem l2NormSq_smul (c : ℂ) (ξ : G →₀ ℂ) :
    l2NormSq (c • ξ) = ‖c‖ ^ 2 * l2NormSq ξ := by
  rw [l2NormSq_eq_sum Finsupp.support_smul, l2NormSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Finsupp.smul_apply, smul_eq_mul, norm_mul, mul_pow]

theorem lTrans_smul (g : G) (c : ℂ) (ξ : G →₀ ℂ) :
    lTrans g (c • ξ) = c • lTrans g ξ := by
  ext x
  rw [lTrans_apply, Finsupp.smul_apply, Finsupp.smul_apply, lTrans_apply]

theorem support_lTrans_subset [DecidableEq G] (g : G) (ξ : G →₀ ℂ) (s : Finset G)
    (hs : ξ.support ⊆ s) :
    (lTrans g ξ).support ⊆ s.image (g * ·) := by
  intro x hx
  rw [Finsupp.mem_support_iff, lTrans_apply] at hx
  exact Finset.mem_image.mpr ⟨g⁻¹ * x, hs (Finsupp.mem_support_iff.mpr hx),
    mul_inv_cancel_left g x⟩

/-! ## Sesquilinear forms of complex matrices -/

section Kernel

variable {Y : Type} [Fintype Y] {ι : Type} [Fintype ι]

theorem sum_swap4 {α : Type*} (T : Finset α) (f : α → ι → Y → Y → ℂ) :
    ∑ x ∈ T, ∑ l, ∑ y, ∑ y', f x l y y' = ∑ l, ∑ y, ∑ y', ∑ x ∈ T, f x l y y' := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [Finset.sum_comm]

/-- The sesquilinear form `∑_{y,y'} conj (v y) * M y y' * w y'` of a complex
matrix, conjugate-linear in the first vector. -/
def qform (M : Matrix Y Y ℂ) (v w : Y → ℂ) : ℂ :=
  ∑ y, ∑ y', (starRingEnd ℂ) (v y) * M y y' * w y'

theorem qform_zero_left (M : Matrix Y Y ℂ) (w : Y → ℂ) : qform M 0 w = 0 := by
  simp [qform]

theorem qform_zero_right (M : Matrix Y Y ℂ) (v : Y → ℂ) : qform M v 0 = 0 := by
  simp [qform]

theorem qform_smul_smul (M : Matrix Y Y ℂ) (c c' : ℂ) (v w : Y → ℂ) :
    qform M (c • v) (c' • w) = (starRingEnd ℂ) c * c' * qform M v w := by
  simp only [qform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun y' _ ↦ ?_
  ring

/-- **Positivity on pairs.**  For every `g`, the block form built from `D 1`,
`D g`, `D g⁻¹` and two vectors is nonnegative. -/
def PairPositive (D : G → Matrix Y Y ℂ) : Prop :=
  ∀ (g : G) (v w : Y → ℂ),
    0 ≤ (qform (D 1) v v + qform (D g) v w + qform (D g⁻¹) w v +
      qform (D 1) w w).re

variable {D : G → Matrix Y Y ℂ}

theorem PairPositive.re_qform_one_nonneg (hD : PairPositive D) (v : Y → ℂ) :
    0 ≤ (qform (D 1) v v).re := by
  have h := hD 1 v 0
  simpa only [qform_zero_left, qform_zero_right, add_zero] using h

/-- **Pair positivity at scale `t`.**  Testing the block form at `(-t b, t⁻¹ a)`
bounds the real part of the cross term. -/
theorem PairPositive.cross_re_le (hD : PairPositive D) (g : G) (a b : Y → ℂ)
    {t : ℝ} (ht : 0 < t) :
    (qform (D g) b a + qform (D g⁻¹) a b).re ≤
      t ^ 2 * (qform (D 1) b b).re + (qform (D 1) a a).re / t ^ 2 := by
  have h := hD g ((-(t : ℂ)) • b) (((t : ℂ)⁻¹) • a)
  rw [qform_smul_smul, qform_smul_smul, qform_smul_smul, qform_smul_smul] at h
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have c1 : (starRingEnd ℂ) (-(t : ℂ)) * (-(t : ℂ)) = ((t ^ 2 : ℝ) : ℂ) := by
    rw [map_neg, Complex.conj_ofReal]
    push_cast
    ring
  have c2 : (starRingEnd ℂ) (-(t : ℂ)) * (t : ℂ)⁻¹ = -1 := by
    rw [map_neg, Complex.conj_ofReal, neg_mul, mul_inv_cancel₀ ht0]
  have c3 : (starRingEnd ℂ) ((t : ℂ)⁻¹) * (-(t : ℂ)) = -1 := by
    rw [map_inv₀, Complex.conj_ofReal, mul_neg, inv_mul_cancel₀ ht0]
  have c4 : (starRingEnd ℂ) ((t : ℂ)⁻¹) * (t : ℂ)⁻¹ = (((t ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [map_inv₀, Complex.conj_ofReal]
    push_cast
    ring
  rw [c1, c2, c3, c4] at h
  simp only [Complex.add_re, Complex.re_ofReal_mul, neg_one_mul, Complex.neg_re] at h
  rw [Complex.add_re, div_eq_inv_mul]
  linarith

/-- The scaled bound, summed over a finite family of vector pairs. -/
theorem PairPositive.sum_cross_re_le (hD : PairPositive D) (g : G)
    (a b : ι → Y → ℂ) {t : ℝ} (ht : 0 < t) :
    (∑ l, (qform (D g) (b l) (a l) + qform (D g⁻¹) (a l) (b l))).re ≤
      t ^ 2 * (∑ l, (qform (D 1) (b l) (b l)).re) +
        (∑ l, (qform (D 1) (a l) (a l)).re) / t ^ 2 := by
  rw [Complex.re_sum, Finset.mul_sum, div_eq_mul_inv, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun l _ ↦ ?_
  rw [← div_eq_mul_inv]
  exact hD.cross_re_le g (a l) (b l) ht

/-! ## Mass, correlations, cross terms -/

/-- The mass of the family at `x`: `∑ₗ Re ⟨v_l(x), D(1) v_l(x)⟩`. -/
noncomputable def mass (D : G → Matrix Y Y ℂ) (d : ι → Y → (G →₀ ℂ)) (x : G) : ℝ :=
  ∑ l, (qform (D 1) (fun y ↦ d l y x) (fun y ↦ d l y x)).re

theorem mass_nonneg (hD : PairPositive D) (d : ι → Y → (G →₀ ℂ)) (x : G) :
    0 ≤ mass D d x :=
  Finset.sum_nonneg fun _ _ ↦ hD.re_qform_one_nonneg _

/-- **The correlation** `∑ₗ ∑_{y,y'} D g y y' ⟪d l y, λ_g (d l y')⟫`. -/
noncomputable def corr (D : G → Matrix Y Y ℂ) (d : ι → Y → (G →₀ ℂ)) (g : G) : ℂ :=
  ∑ l, ∑ y, ∑ y', D g y y' * starInner (d l y) (lTrans g (d l y'))

/-- The pointwise cross term. -/
noncomputable def cross (D : G → Matrix Y Y ℂ) (d : ι → Y → (G →₀ ℂ)) (g x : G) : ℂ :=
  ∑ l, (qform (D g) (fun y ↦ d l y x) (fun y ↦ d l y (g⁻¹ * x)) +
    qform (D g⁻¹) (fun y ↦ d l y (g⁻¹ * x)) (fun y ↦ d l y x))

theorem cross_re_le_sqrt (hD : PairPositive D) (d : ι → Y → (G →₀ ℂ)) (g x : G) :
    (cross D d g x).re ≤
      2 * Real.sqrt (mass D d (g⁻¹ * x)) * Real.sqrt (mass D d x) :=
  le_two_mul_sqrt_mul_sqrt (mass_nonneg hD d (g⁻¹ * x)) (mass_nonneg hD d x)
    fun _ ht ↦ hD.sum_cross_re_le g (fun l y ↦ d l y (g⁻¹ * x))
      (fun l y ↦ d l y x) ht

variable [DecidableEq G]

/-- A finite set carrying every vector of the family. -/
def supp (d : ι → Y → (G →₀ ℂ)) : Finset G :=
  Finset.univ.biUnion fun l ↦ Finset.univ.biUnion fun y ↦ (d l y).support

omit [Group G] in
theorem support_subset_supp (d : ι → Y → (G →₀ ℂ)) (l : ι) (y : Y) :
    (d l y).support ⊆ supp d := fun _ hx ↦
  Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _,
    Finset.mem_biUnion.mpr ⟨y, Finset.mem_univ _, hx⟩⟩

omit [Group G] in
theorem eq_zero_of_not_mem_supp {d : ι → Y → (G →₀ ℂ)} {x : G}
    (hx : x ∉ supp d) (l : ι) (y : Y) : d l y x = 0 :=
  Finsupp.notMem_support_iff.mp fun h ↦ hx (support_subset_supp d l y h)

theorem mass_eq_zero_of_not_mem_supp {d : ι → Y → (G →₀ ℂ)} {x : G}
    (hx : x ∉ supp d) : mass D d x = 0 := by
  simp [mass, qform, eq_zero_of_not_mem_supp hx]

/-- **The Reiter vector** `x ↦ √(mass x)`, finitely supported on `supp d`. -/
noncomputable def reiter (D : G → Matrix Y Y ℂ) (d : ι → Y → (G →₀ ℂ)) : G →₀ ℂ :=
  Finsupp.onFinset (supp d) (fun x ↦ ((Real.sqrt (mass D d x) : ℝ) : ℂ))
    fun x hx ↦ by
      by_contra hmem
      exact hx (by simp only [mass_eq_zero_of_not_mem_supp hmem, Real.sqrt_zero,
        Complex.ofReal_zero])

theorem reiter_apply (D : G → Matrix Y Y ℂ) (d : ι → Y → (G →₀ ℂ)) (x : G) :
    reiter D d x = ((Real.sqrt (mass D d x) : ℝ) : ℂ) :=
  Finsupp.onFinset_apply

theorem support_reiter_subset (D : G → Matrix Y Y ℂ) (d : ι → Y → (G →₀ ℂ)) :
    (reiter D d).support ⊆ supp d :=
  Finsupp.support_onFinset_subset

theorem norm_reiter_sq (hD : PairPositive D) (d : ι → Y → (G →₀ ℂ)) (x : G) :
    ‖reiter D d x‖ ^ 2 = mass D d x := by
  rw [reiter_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (mass_nonneg hD d x)]

/-- The correlation as a sum over points. -/
theorem corr_eq_sum (D : G → Matrix Y Y ℂ) (d : ι → Y → (G →₀ ℂ)) (g : G)
    {T : Finset G} (hT : supp d ⊆ T) :
    corr D d g =
      ∑ x ∈ T, ∑ l, qform (D g) (fun y ↦ d l y x) (fun y ↦ d l y (g⁻¹ * x)) := by
  symm
  simp only [qform]
  refine (sum_swap4 T _).trans ?_
  rw [corr]
  refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun y _ ↦
    Finset.sum_congr rfl fun y' _ ↦ ?_
  rw [starInner_eq_sum ((support_subset_supp d l y).trans hT), Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [lTrans_apply]
  ring

/-- The correlation at `g⁻¹` as a sum over points, paired against `λ_g`. -/
theorem corr_inv_eq_sum (D : G → Matrix Y Y ℂ) (d : ι → Y → (G →₀ ℂ)) (g : G)
    {T : Finset G} (hT' : (supp d).image (g * ·) ⊆ T) :
    corr D d g⁻¹ =
      ∑ x ∈ T, ∑ l, qform (D g⁻¹) (fun y ↦ d l y (g⁻¹ * x)) (fun y ↦ d l y x) := by
  symm
  simp only [qform]
  refine (sum_swap4 T _).trans ?_
  rw [corr]
  refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun y _ ↦
    Finset.sum_congr rfl fun y' _ ↦ ?_
  rw [← starInner_lTrans_left,
    starInner_eq_sum ((support_lTrans_subset g (d l y) (supp d)
      (support_subset_supp d l y)).trans hT'), Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [lTrans_apply]
  ring

/-- **The norm of the Reiter vector** is the real part of the correlation at `1`. -/
theorem l2NormSq_reiter (hD : PairPositive D) (d : ι → Y → (G →₀ ℂ)) :
    l2NormSq (reiter D d) = (corr D d 1).re := by
  rw [l2NormSq_eq_sum (support_reiter_subset D d),
    corr_eq_sum D d 1 (Finset.Subset.refl _), Complex.re_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [norm_reiter_sq hD, mass, Complex.re_sum]
  simp only [inv_one, one_mul]

/-- **The Reiter estimate.** -/
theorem l2NormSq_lTrans_sub_reiter_le (hD : PairPositive D)
    (d : ι → Y → (G →₀ ℂ)) (g : G) :
    l2NormSq (lTrans g (reiter D d) - reiter D d) ≤
      2 * (corr D d 1).re - (corr D d g).re - (corr D d g⁻¹).re := by
  set T : Finset G := supp d ∪ (supp d).image (g * ·)
  have hsuppT : supp d ⊆ T := Finset.subset_union_left
  have himT : (supp d).image (g * ·) ⊆ T := Finset.subset_union_right
  have hζT : (reiter D d).support ⊆ T := (support_reiter_subset D d).trans hsuppT
  have hlζT : (lTrans g (reiter D d)).support ⊆ T :=
    (support_lTrans_subset g (reiter D d) (supp d) (support_reiter_subset D d)).trans
      himT
  have hdiffT : (lTrans g (reiter D d) - reiter D d).support ⊆ T :=
    Finsupp.support_sub.trans (Finset.union_subset hlζT hζT)
  have hpt : ∀ x ∈ T, ‖(lTrans g (reiter D d) - reiter D d) x‖ ^ 2 ≤
      mass D d (g⁻¹ * x) + mass D d x - (cross D d g x).re := by
    intro x _
    rw [Finsupp.sub_apply, lTrans_apply, reiter_apply, reiter_apply,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact sqrt_sub_sqrt_sq_le (mass_nonneg hD d (g⁻¹ * x)) (mass_nonneg hD d x)
      (cross_re_le_sqrt hD d g x)
  have e1 : ∑ x ∈ T, mass D d (g⁻¹ * x) = (corr D d 1).re := by
    rw [← l2NormSq_reiter hD d, ← l2NormSq_lTrans g (reiter D d),
      l2NormSq_eq_sum hlζT]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [lTrans_apply, norm_reiter_sq hD]
  have e2 : ∑ x ∈ T, mass D d x = (corr D d 1).re := by
    rw [← l2NormSq_reiter hD d, l2NormSq_eq_sum hζT]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [norm_reiter_sq hD]
  have e3 : ∑ x ∈ T, cross D d g x = corr D d g + corr D d g⁻¹ := by
    rw [corr_eq_sum D d g hsuppT, corr_inv_eq_sum D d g himT,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [cross, ← Finset.sum_add_distrib]
  calc l2NormSq (lTrans g (reiter D d) - reiter D d)
      = ∑ x ∈ T, ‖(lTrans g (reiter D d) - reiter D d) x‖ ^ 2 :=
        l2NormSq_eq_sum hdiffT
    _ ≤ ∑ x ∈ T, (mass D d (g⁻¹ * x) + mass D d x - (cross D d g x).re) :=
        Finset.sum_le_sum hpt
    _ = (∑ x ∈ T, mass D d (g⁻¹ * x)) + (∑ x ∈ T, mass D d x) -
          (∑ x ∈ T, cross D d g x).re := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Complex.re_sum]
    _ = 2 * (corr D d 1).re - (corr D d g).re - (corr D d g⁻¹).re := by
        rw [e1, e2, e3, Complex.add_re]
        ring

/-- **Correlations near one give almost invariant unit vectors.** -/
theorem exists_almostInvariant_of_corr (hD : PairPositive D)
    (d : ι → Y → (G →₀ ℂ)) (F : Finset G) {δ : ℝ} (hδ : δ ≤ 1 / 4)
    (h1 : ‖corr D d 1 - 1‖ ≤ δ)
    (hF : ∀ g ∈ F, ‖corr D d g - 1‖ ≤ δ ∧ ‖corr D d g⁻¹ - 1‖ ≤ δ) :
    ∃ ξ : G →₀ ℂ, l2NormSq ξ = 1 ∧
      ∀ g ∈ F, l2NormSq (lTrans g ξ - ξ) ≤ 8 * δ := by
  have hre : ∀ z : ℂ, |z.re - 1| ≤ ‖z - 1‖ := fun z ↦ by
    have hz := Complex.abs_re_le_norm (z - 1)
    rwa [Complex.sub_re, Complex.one_re] at hz
  have hr1 := (hre (corr D d 1)).trans h1
  have hr34 : 3 / 4 ≤ (corr D d 1).re := by
    have := (abs_le.mp hr1).1
    linarith
  have hr0 : 0 < (corr D d 1).re := by linarith
  set c : ℂ := (((Real.sqrt (corr D d 1).re)⁻¹ : ℝ) : ℂ) with hc
  have hcn : ‖c‖ ^ 2 = ((corr D d 1).re)⁻¹ := by
    rw [hc, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
      Real.sq_sqrt hr0.le]
  refine ⟨c • reiter D d, ?_, fun g hg ↦ ?_⟩
  · rw [l2NormSq_smul, hcn, l2NormSq_reiter hD d, inv_mul_cancel₀ hr0.ne']
  · rw [lTrans_smul, ← smul_sub, l2NormSq_smul, hcn]
    have hb := l2NormSq_lTrans_sub_reiter_le hD d g
    obtain ⟨hg1, hg2⟩ := hF g hg
    have e1 := (abs_le.mp ((hre _).trans hg1)).1
    have e2 := (abs_le.mp ((hre _).trans hg2)).1
    have e0 := (abs_le.mp hr1).2
    have hnum : l2NormSq (lTrans g (reiter D d) - reiter D d) ≤ 4 * δ := by
      linarith
    have hnn : 0 ≤ l2NormSq (lTrans g (reiter D d) - reiter D d) :=
      l2NormSq_nonneg _
    have hinv : ((corr D d 1).re)⁻¹ ≤ 2 := by
      rw [inv_eq_one_div, div_le_iff₀ hr0]
      linarith
    calc ((corr D d 1).re)⁻¹ * l2NormSq (lTrans g (reiter D d) - reiter D d)
        ≤ 2 * (4 * δ) :=
          mul_le_mul hinv hnum hnn (by norm_num)
      _ = 8 * δ := by ring

end Kernel

end LanceMaximal
end GroupApproximation

open GroupApproximation.LanceMaximal

#audit_axioms GroupApproximation.LanceMaximal.le_two_mul_sqrt_mul_sqrt
#audit_axioms GroupApproximation.LanceMaximal.l2NormSq_reiter
#audit_axioms GroupApproximation.LanceMaximal.l2NormSq_lTrans_sub_reiter_le
#audit_axioms GroupApproximation.LanceMaximal.exists_almostInvariant_of_corr
