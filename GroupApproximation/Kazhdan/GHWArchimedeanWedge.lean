import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Determinant
import GroupApproximation.Meta.AxiomGuard

/-!
# Wedges in the Lorentz shell

Guentner--Higson--Weinberger, *The Novikov conjecture for linear groups* (Publ. Math. IHÉS 101
(2005)), §5, build the negative-type function at an archimedean place from the walls of
hyperbolic space.  In the coordinates of `Kazhdan/GHWArchimedeanMinkowski`
(`v ↦ [[v₀, v₂ + i v₃], [v₂ − i v₃, v₁]]`, `Q v = v₀v₁ − v₂² − v₃²`), a wall is a space-like
vector in the shell `1 ≤ −Q ≤ 2`.  The walls separating the base point `diag(1, 1)` from
`diag(eʳ, e⁻ʳ)` contain the **wedge**

  `W(s, t) = {v ∈ shell : s·v₀² < −v₀v₁ < t·v₀²}`,  with `(s, t) = (e^{−2r}, 1)`.

This module is the measure theory of the wedges, in coordinates only.

* `wedge_subset_closedBall`, `volume_wedge_lt_top`, `volume_wedge_pos`: for `0 < s < t` the
  wedge is bounded and contains a nonempty open set, so `0 < vol W(s, t) < ∞`.
* `measurePreserving_hypScale`, `volume_wedge_scale`: the hyperbolic scaling
  `(v₀, v₁, v₂, v₃) ↦ (eᵗv₀, e⁻ᵗv₁, v₂, v₃)` preserves volume (determinant `1`) and carries
  `W(e^{2τ}s, e^{2τ}t)` onto `W(s, t)`.
* `wedgePhi_add`, `wedgePhi_monotoneOn`, `wedgePhi_eq_mul`: `φ(u) = vol W(1, eᵘ)` is additive
  (the dividing hyperplane `v₁ + k v₀ = 0` is null) and monotone, hence `φ(u) = u·φ(1)`, with
  `φ(1) > 0`.
* `sep_subset_closedBall`, `wedge_sep_of_nonneg_side`, `wedge_sep_of_nonpos_side`,
  `volume_sep_ge`: for `a, b > 0` the shell vectors with `(v₀ + v₁)(b v₀ + a v₁) ≤ 0` form a
  bounded set, it contains the wedge `W(e^{−2r}, 1)` or `W(1, e^{−2r})` for `(a, b) = (eʳ, e⁻ʳ)`,
  and so its volume is at least `2|r|·φ(1)`.

`Kazhdan/GHWArchimedeanSeparation` transports these statements to the half-spaces of
`Kazhdan/GHWArchimedeanWalls` by the spectral theorem.

## Manuscript status

Infrastructure for the Toeplitz--Jacobson remark (tex line 1146, "every countable subgroup of
`GL_2` over a field has the Haagerup property [GHW, Theorem 4]"); certifies no printed sentence
on its own.
-/

namespace GroupApproximation
namespace GHW
namespace Wedge

open MeasureTheory Set

noncomputable section

/-! ## Monotone additive functions on the half-line -/

/-- **A monotone additive function on `[0, ∞)` is linear.** -/
theorem eq_mul_of_additive_monotoneOn {φ : ℝ → ℝ}
    (hadd : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → φ (u + v) = φ u + φ v)
    (hmono : MonotoneOn φ (Ici 0)) {u : ℝ} (hu : 0 ≤ u) :
    φ u = u * φ 1 := by
  have h0 : φ 0 = 0 := by
    have h := hadd 0 0 le_rfl le_rfl
    rw [add_zero] at h
    linarith
  have hnat : ∀ (n : ℕ) (x : ℝ), 0 ≤ x → φ (n * x) = n * φ x := by
    intro n x hx
    induction n with
    | zero => rw [Nat.cast_zero, zero_mul, zero_mul, h0]
    | succ k ih =>
      have hkx : 0 ≤ (k : ℝ) * x := mul_nonneg (Nat.cast_nonneg k) hx
      rw [Nat.cast_succ, add_mul, one_mul, hadd _ _ hkx hx, ih, add_mul, one_mul]
  have h1 : 0 ≤ φ 1 := by
    have h := hmono (show (0 : ℝ) ∈ Ici 0 from le_rfl) (show (1 : ℝ) ∈ Ici 0 from zero_le_one)
      zero_le_one
    rwa [h0] at h
  have hbound : ∀ n : ℕ, (n : ℝ) * |φ u - u * φ 1| ≤ φ 1 := by
    intro n
    have hnu : 0 ≤ (n : ℝ) * u := mul_nonneg (Nat.cast_nonneg n) hu
    have hlo : (⌊(n : ℝ) * u⌋₊ : ℝ) ≤ n * u := Nat.floor_le hnu
    have hhi : (n : ℝ) * u < ⌊(n : ℝ) * u⌋₊ + 1 := Nat.lt_floor_add_one _
    have em : φ (⌊(n : ℝ) * u⌋₊ : ℝ) = ⌊(n : ℝ) * u⌋₊ * φ 1 := by
      have h := hnat ⌊(n : ℝ) * u⌋₊ 1 zero_le_one
      rwa [mul_one] at h
    have em1 : φ ((⌊(n : ℝ) * u⌋₊ : ℝ) + 1) = ⌊(n : ℝ) * u⌋₊ * φ 1 + φ 1 := by
      have h := hnat (⌊(n : ℝ) * u⌋₊ + 1) 1 zero_le_one
      rw [mul_one, Nat.cast_succ, add_mul, one_mul] at h
      exact h
    have hm1 : ((⌊(n : ℝ) * u⌋₊ : ℝ)) ∈ Ici (0 : ℝ) := Nat.cast_nonneg _
    have hm2 : ((⌊(n : ℝ) * u⌋₊ : ℝ) + 1) ∈ Ici (0 : ℝ) := by
      show (0 : ℝ) ≤ _
      positivity
    have hA : (⌊(n : ℝ) * u⌋₊ : ℝ) * φ 1 ≤ n * φ u := by
      rw [← em, ← hnat n u hu]
      exact hmono hm1 hnu hlo
    have hB : (n : ℝ) * φ u ≤ ⌊(n : ℝ) * u⌋₊ * φ 1 + φ 1 := by
      rw [← em1, ← hnat n u hu]
      exact hmono hnu hm2 hhi.le
    have hC : (⌊(n : ℝ) * u⌋₊ : ℝ) * φ 1 ≤ (n * u) * φ 1 := mul_le_mul_of_nonneg_right hlo h1
    have hD : ((n : ℝ) * u) * φ 1 ≤ ⌊(n : ℝ) * u⌋₊ * φ 1 + φ 1 := by
      have h := mul_le_mul_of_nonneg_right hhi.le h1
      rwa [add_mul, one_mul] at h
    have key : |(n : ℝ) * φ u - ((n : ℝ) * u) * φ 1| ≤ φ 1 :=
      abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    have e : (n : ℝ) * φ u - ((n : ℝ) * u) * φ 1 = n * (φ u - u * φ 1) := by ring
    rw [e, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)] at key
    exact key
  by_contra hne
  have hpos : 0 < |φ u - u * φ 1| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := exists_nat_gt (φ 1 / |φ u - u * φ 1|)
  rw [div_lt_iff₀ hpos] at hn
  linarith [hbound n]

/-! ## The shell and the wedges -/

/-- The shell `1 ≤ −Q ≤ 2`, `Q v = v₀v₁ − v₂² − v₃²`. -/
def wedgeShell : Set (Fin 4 → ℝ) :=
  {v | 1 ≤ -(v 0 * v 1 - v 2 ^ 2 - v 3 ^ 2) ∧ -(v 0 * v 1 - v 2 ^ 2 - v 3 ^ 2) ≤ 2}

/-- **The wedge** `W(s, t) = {v ∈ shell : s·v₀² < −v₀v₁ < t·v₀²}`. -/
def wedge (s t : ℝ) : Set (Fin 4 → ℝ) :=
  {v | v ∈ wedgeShell ∧ s * v 0 ^ 2 < -(v 0 * v 1) ∧ -(v 0 * v 1) < t * v 0 ^ 2}

theorem isClosed_wedgeShell : IsClosed wedgeShell := by
  have hQ : Continuous fun v : Fin 4 → ℝ ↦ -(v 0 * v 1 - v 2 ^ 2 - v 3 ^ 2) := by fun_prop
  exact (isClosed_le continuous_const hQ).inter (isClosed_le hQ continuous_const)

theorem measurableSet_wedge (s t : ℝ) : MeasurableSet (wedge s t) := by
  have h1 : IsOpen {v : Fin 4 → ℝ | s * v 0 ^ 2 < -(v 0 * v 1)} :=
    isOpen_lt (by fun_prop) (by fun_prop)
  have h2 : IsOpen {v : Fin 4 → ℝ | -(v 0 * v 1) < t * v 0 ^ 2} :=
    isOpen_lt (by fun_prop) (by fun_prop)
  exact isClosed_wedgeShell.measurableSet.inter (h1.measurableSet.inter h2.measurableSet)

theorem abs_le_sq_add_one (x : ℝ) : |x| ≤ x ^ 2 + 1 := by
  nlinarith [sq_nonneg (|x| - 1), sq_abs x, abs_nonneg x, sq_nonneg x]

/-- A vector whose squared coordinates sum to at most `M` lies in the closed ball of radius
`M + 1`. -/
theorem mem_closedBall_of_sum_sq_le {v : Fin 4 → ℝ} {M : ℝ} (hM : ∑ j, v j ^ 2 ≤ M) :
    v ∈ Metric.closedBall 0 (M + 1) := by
  have hM0 : 0 ≤ M := le_trans (Finset.sum_nonneg fun j _ ↦ sq_nonneg (v j)) hM
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by linarith)]
  intro i
  rw [Real.norm_eq_abs]
  have hi : v i ^ 2 ≤ ∑ j, v j ^ 2 :=
    Finset.single_le_sum (fun j _ ↦ sq_nonneg (v j)) (Finset.mem_univ i)
  linarith [abs_le_sq_add_one (v i)]

/-- **The wedge is bounded.** -/
theorem wedge_subset_closedBall {s t : ℝ} (hs : 0 < s) :
    wedge s t ⊆ Metric.closedBall 0 (t ^ 2 * (2 / s) + 2 / s + 2 + 1) := by
  rintro v ⟨⟨-, hQ2⟩, h1, h2⟩
  have hneg : 0 < -(v 0 * v 1) := lt_of_le_of_lt (mul_nonneg hs.le (sq_nonneg _)) h1
  have h23 : v 2 ^ 2 + v 3 ^ 2 ≤ 2 := by linarith
  have h0sq : v 0 ^ 2 ≤ 2 / s := by
    rw [le_div_iff₀ hs]
    nlinarith [sq_nonneg (v 2), sq_nonneg (v 3)]
  have hv0 : 0 < v 0 ^ 2 := by
    rcases eq_or_ne (v 0) 0 with h | h
    · rw [h] at hneg
      simp at hneg
    · positivity
  have h1sq : v 1 ^ 2 ≤ t ^ 2 * (2 / s) := by
    have h3 : (-(v 0 * v 1)) ^ 2 < (t * v 0 ^ 2) ^ 2 := pow_lt_pow_left₀ h2 hneg.le two_ne_zero
    have h4 : v 1 ^ 2 * v 0 ^ 2 < t ^ 2 * v 0 ^ 2 * v 0 ^ 2 := by linarith
    have h5 : v 1 ^ 2 < t ^ 2 * v 0 ^ 2 := lt_of_mul_lt_mul_right h4 hv0.le
    calc v 1 ^ 2 ≤ t ^ 2 * v 0 ^ 2 := h5.le
      _ ≤ t ^ 2 * (2 / s) := mul_le_mul_of_nonneg_left h0sq (sq_nonneg t)
  apply mem_closedBall_of_sum_sq_le
  rw [Fin.sum_univ_four]
  linarith

/-- **The wedge has finite volume.** -/
theorem volume_wedge_lt_top {s t : ℝ} (hs : 0 < s) : volume (wedge s t) < ⊤ :=
  (Metric.isBounded_closedBall.subset (wedge_subset_closedBall hs)).measure_lt_top

/-- **The wedge has positive volume**: it contains a nonempty open set. -/
theorem volume_wedge_pos {s t : ℝ} (hs : 0 < s) (hst : s < t) : 0 < volume (wedge s t) := by
  obtain ⟨l, hsl, hlt⟩ : ∃ l, s < l ∧ l < t := ⟨(s + t) / 2, by linarith, by linarith⟩
  have hl0 : 0 < l := hs.trans hsl
  have hl1 : (0 : ℝ) < l + 1 := by linarith
  obtain ⟨δ, hδ0, hδl⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * (l + 1) = 1 :=
    ⟨(l + 1)⁻¹, inv_pos.mpr hl1, inv_mul_cancel₀ hl1.ne'⟩
  have hlδ : l * δ ^ 2 < 1 := by
    have e : (δ * (l + 1)) ^ 2 = 1 := by rw [hδl, one_pow]
    have hlt' : l * δ ^ 2 < (δ * (l + 1)) ^ 2 := by
      nlinarith [sq_nonneg (δ * l), mul_pos (pow_pos hδ0 2) hl0, pow_pos hδ0 2]
    linarith
  have hδ2 : 0 < δ ^ 2 := pow_pos hδ0 2
  have hO : IsOpen ({v : Fin 4 → ℝ | 1 < -(v 0 * v 1 - v 2 ^ 2 - v 3 ^ 2)} ∩
      ({v | -(v 0 * v 1 - v 2 ^ 2 - v 3 ^ 2) < 2} ∩
        ({v | s * v 0 ^ 2 < -(v 0 * v 1)} ∩ {v | -(v 0 * v 1) < t * v 0 ^ 2}))) :=
    (isOpen_lt (by fun_prop) (by fun_prop)).inter
      ((isOpen_lt (by fun_prop) (by fun_prop)).inter
        ((isOpen_lt (by fun_prop) (by fun_prop)).inter (isOpen_lt (by fun_prop) (by fun_prop))))
  have hsub : ({v : Fin 4 → ℝ | 1 < -(v 0 * v 1 - v 2 ^ 2 - v 3 ^ 2)} ∩
      ({v | -(v 0 * v 1 - v 2 ^ 2 - v 3 ^ 2) < 2} ∩
        ({v | s * v 0 ^ 2 < -(v 0 * v 1)} ∩ {v | -(v 0 * v 1) < t * v 0 ^ 2}))) ⊆
      wedge s t := by
    rintro v ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1.le, h2.le⟩, h3, h4⟩
  let p : Fin 4 → ℝ := ![δ, -(l * δ), 1, 0]
  have p0 : p 0 = δ := rfl
  have p1 : p 1 = -(l * δ) := rfl
  have p2 : p 2 = 1 := rfl
  have p3 : p 3 = 0 := rfl
  have hxy : p 0 * p 1 = -(l * δ ^ 2) := by rw [p0, p1]; ring
  have hQ : -(p 0 * p 1 - p 2 ^ 2 - p 3 ^ 2) = l * δ ^ 2 + 1 := by rw [hxy, p2, p3]; ring
  have hp : p ∈ ({v : Fin 4 → ℝ | 1 < -(v 0 * v 1 - v 2 ^ 2 - v 3 ^ 2)} ∩
      ({v | -(v 0 * v 1 - v 2 ^ 2 - v 3 ^ 2) < 2} ∩
        ({v | s * v 0 ^ 2 < -(v 0 * v 1)} ∩ {v | -(v 0 * v 1) < t * v 0 ^ 2}))) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · show 1 < -(p 0 * p 1 - p 2 ^ 2 - p 3 ^ 2)
      rw [hQ]
      nlinarith [mul_pos hl0 hδ2]
    · show -(p 0 * p 1 - p 2 ^ 2 - p 3 ^ 2) < 2
      rw [hQ]
      linarith
    · show s * p 0 ^ 2 < -(p 0 * p 1)
      rw [hxy, neg_neg, p0]
      exact mul_lt_mul_of_pos_right hsl hδ2
    · show -(p 0 * p 1) < t * p 0 ^ 2
      rw [hxy, neg_neg, p0]
      exact mul_lt_mul_of_pos_right hlt hδ2
  exact (hO.measure_pos volume ⟨p, hp⟩).trans_le (measure_mono hsub)

/-! ## The hyperbolic scaling -/

/-- **The hyperbolic scaling** `(v₀, v₁, v₂, v₃) ↦ (eᵗv₀, e⁻ᵗv₁, v₂, v₃)`. -/
def hypScale (τ : ℝ) : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) :=
  Matrix.toLin' (Matrix.diagonal ![Real.exp τ, Real.exp (-τ), 1, 1])

theorem hypScale_apply (τ : ℝ) (v : Fin 4 → ℝ) (i : Fin 4) :
    hypScale τ v i = ![Real.exp τ, Real.exp (-τ), 1, 1] i * v i := by
  rw [hypScale, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

theorem det_hypScale (τ : ℝ) : LinearMap.det (hypScale τ) = 1 := by
  rw [hypScale, LinearMap.det_toLin', Matrix.det_diagonal, Fin.prod_univ_four]
  show Real.exp τ * Real.exp (-τ) * 1 * 1 = 1
  rw [mul_one, mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- **The hyperbolic scaling preserves volume** (its determinant is `1`). -/
theorem measurePreserving_hypScale (τ : ℝ) :
    MeasurePreserving (hypScale τ) (volume : Measure (Fin 4 → ℝ)) volume := by
  refine ⟨(LinearMap.continuous_of_finiteDimensional (hypScale τ)).measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume
      (by rw [det_hypScale]; exact one_ne_zero),
    det_hypScale, inv_one, abs_one, ENNReal.ofReal_one, one_smul]

/-- The scaling preserves `Q`, hence the shell, and multiplies the wedge parameters by
`e^{2τ}`. -/
theorem hypScale_preimage_wedge (τ s t : ℝ) :
    hypScale τ ⁻¹' wedge s t = wedge (Real.exp (2 * τ) * s) (Real.exp (2 * τ) * t) := by
  ext v
  have h0 : hypScale τ v 0 = Real.exp τ * v 0 := hypScale_apply τ v 0
  have h1 : hypScale τ v 1 = Real.exp (-τ) * v 1 := hypScale_apply τ v 1
  have h2 : hypScale τ v 2 = v 2 := by
    rw [hypScale_apply]
    exact one_mul _
  have h3 : hypScale τ v 3 = v 3 := by
    rw [hypScale_apply]
    exact one_mul _
  have hxy : Real.exp τ * v 0 * (Real.exp (-τ) * v 1) = v 0 * v 1 := by
    calc Real.exp τ * v 0 * (Real.exp (-τ) * v 1)
        = (Real.exp τ * Real.exp (-τ)) * (v 0 * v 1) := by ring
      _ = v 0 * v 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  have hsq : ∀ c : ℝ, c * (Real.exp τ * v 0) ^ 2 = Real.exp (2 * τ) * c * v 0 ^ 2 := by
    intro c
    rw [mul_pow, sq (Real.exp τ), ← Real.exp_add, ← two_mul]
    ring
  simp only [Set.mem_preimage, wedge, wedgeShell, Set.mem_setOf_eq, h0, h1, h2, h3, hxy, hsq]

/-- **The wedge volume depends only on the ratio of the parameters.** -/
theorem volume_wedge_scale (τ s t : ℝ) :
    volume (wedge (Real.exp (2 * τ) * s) (Real.exp (2 * τ) * t)) = volume (wedge s t) := by
  rw [← hypScale_preimage_wedge]
  exact (measurePreserving_hypScale τ).measure_preimage
    (measurableSet_wedge s t).nullMeasurableSet

/-! ## Additivity -/

/-- The hyperplane `v₁ + k v₀ = 0` is null. -/
theorem volume_line (k : ℝ) : volume {v : Fin 4 → ℝ | v 1 + k * v 0 = 0} = 0 := by
  let ℓ : (Fin 4 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 1 + k • LinearMap.proj 0
  have hset : {v : Fin 4 → ℝ | v 1 + k * v 0 = 0} = (LinearMap.ker ℓ : Set (Fin 4 → ℝ)) := by
    ext v
    simp [ℓ]
  have hne : LinearMap.ker ℓ ≠ ⊤ := by
    intro h
    have hmem : (Pi.single 1 1 : Fin 4 → ℝ) ∈ LinearMap.ker ℓ := by
      rw [h]
      exact Submodule.mem_top
    simp [ℓ] at hmem
  rw [hset]
  exact Measure.addHaar_submodule volume _ hne

theorem wedge_mono {s s' t t' : ℝ} (hs : s' ≤ s) (ht : t ≤ t') :
    wedge s t ⊆ wedge s' t' := by
  rintro v ⟨hv, h1, h2⟩
  exact ⟨hv, lt_of_le_of_lt (mul_le_mul_of_nonneg_right hs (sq_nonneg _)) h1,
    lt_of_lt_of_le h2 (mul_le_mul_of_nonneg_right ht (sq_nonneg _))⟩

theorem disjoint_wedge (s k t : ℝ) : Disjoint (wedge s k) (wedge k t) := by
  rw [Set.disjoint_left]
  rintro v ⟨-, -, h1⟩ ⟨-, h2, -⟩
  exact lt_irrefl _ (h1.trans h2)

theorem wedge_subset_union (s k t : ℝ) :
    wedge s t ⊆ wedge s k ∪ wedge k t ∪ {v : Fin 4 → ℝ | v 1 + k * v 0 = 0} := by
  rintro v ⟨hv, h1, h2⟩
  rcases lt_trichotomy (-(v 0 * v 1)) (k * v 0 ^ 2) with h | h | h
  · exact Or.inl (Or.inl ⟨hv, h1, h⟩)
  · refine Or.inr ?_
    have hx : v 0 ≠ 0 := by
      intro hx0
      rw [hx0] at h1
      simp at h1
    have h3 : v 0 * (v 1 + k * v 0) = 0 := by linear_combination -h
    exact (mul_eq_zero.mp h3).resolve_left hx
  · exact Or.inl (Or.inr ⟨hv, h, h2⟩)

/-- **The wedge volume is additive in the parameters.** -/
theorem volume_wedge_add {s k t : ℝ} (hsk : s ≤ k) (hkt : k ≤ t) :
    volume (wedge s t) = volume (wedge s k) + volume (wedge k t) := by
  rw [← measure_union (disjoint_wedge s k t) (measurableSet_wedge k t)]
  refine le_antisymm ?_
    (measure_mono (Set.union_subset (wedge_mono le_rfl hkt) (wedge_mono hsk le_rfl)))
  calc volume (wedge s t)
      ≤ volume (wedge s k ∪ wedge k t ∪ {v : Fin 4 → ℝ | v 1 + k * v 0 = 0}) :=
        measure_mono (wedge_subset_union s k t)
    _ ≤ volume (wedge s k ∪ wedge k t) + volume {v : Fin 4 → ℝ | v 1 + k * v 0 = 0} :=
        measure_union_le _ _
    _ = volume (wedge s k ∪ wedge k t) := by rw [volume_line, add_zero]

/-! ## `φ(u) = vol W(1, eᵘ)` is linear -/

/-- `φ(u) = vol W(1, eᵘ)`. -/
def wedgePhi (u : ℝ) : ℝ := (volume (wedge 1 (Real.exp u))).toReal

theorem wedgePhi_add {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    wedgePhi (u + v) = wedgePhi u + wedgePhi v := by
  have h1 : (1 : ℝ) ≤ Real.exp u := Real.one_le_exp hu
  have h2 : Real.exp u ≤ Real.exp (u + v) := Real.exp_le_exp.mpr (by linarith)
  have hscale : volume (wedge (Real.exp u) (Real.exp (u + v))) =
      volume (wedge 1 (Real.exp v)) := by
    have h := volume_wedge_scale (u / 2) 1 (Real.exp v)
    rwa [show 2 * (u / 2) = u by ring, mul_one, ← Real.exp_add] at h
  unfold wedgePhi
  rw [volume_wedge_add h1 h2, hscale,
    ENNReal.toReal_add (volume_wedge_lt_top one_pos).ne (volume_wedge_lt_top one_pos).ne]

theorem wedgePhi_monotoneOn : MonotoneOn wedgePhi (Ici 0) := by
  intro u _ u' _ huu'
  exact ENNReal.toReal_mono (volume_wedge_lt_top one_pos).ne
    (measure_mono (wedge_mono le_rfl (Real.exp_le_exp.mpr huu')))

/-- **`φ(u) = u·φ(1)`.** -/
theorem wedgePhi_eq_mul {u : ℝ} (hu : 0 ≤ u) : wedgePhi u = u * wedgePhi 1 :=
  eq_mul_of_additive_monotoneOn (fun _ _ hu hv ↦ wedgePhi_add hu hv) wedgePhi_monotoneOn hu

theorem wedgePhi_one_pos : 0 < wedgePhi 1 := by
  have he : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (one_ne_zero (α := ℝ))
    linarith
  exact ENNReal.toReal_pos (volume_wedge_pos one_pos he).ne' (volume_wedge_lt_top one_pos).ne

/-! ## Separation at diagonal points -/

/-- **The separating shell vectors are bounded**: for `a, b > 0` the shell vectors with
`(v₀ + v₁)(b v₀ + a v₁) ≤ 0` lie in a closed ball. -/
theorem sep_subset_closedBall {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    {v : Fin 4 → ℝ | v ∈ wedgeShell ∧ (v 0 + v 1) * (b * v 0 + a * v 1) ≤ 0} ⊆
      Metric.closedBall 0 (2 + 2 * (2 * (a + b) / b + 2 * (a + b) / a) + 1) := by
  rintro v ⟨⟨-, hQ2⟩, hpq⟩
  have hprod : -(v 0 * v 1) ≤ 2 := by nlinarith [sq_nonneg (v 2), sq_nonneg (v 3)]
  have hsum : b * v 0 ^ 2 + a * v 1 ^ 2 ≤ 2 * (a + b) := by
    nlinarith [mul_le_mul_of_nonneg_left hprod (add_pos ha hb).le]
  have h0 : v 0 ^ 2 ≤ 2 * (a + b) / b := by
    rw [le_div_iff₀ hb]
    nlinarith [mul_nonneg ha.le (sq_nonneg (v 1))]
  have h1 : v 1 ^ 2 ≤ 2 * (a + b) / a := by
    rw [le_div_iff₀ ha]
    nlinarith [mul_nonneg hb.le (sq_nonneg (v 0))]
  have h23 : v 2 ^ 2 + v 3 ^ 2 ≤ 2 + (v 0 ^ 2 + v 1 ^ 2) / 2 := by
    nlinarith [sq_nonneg (v 0 - v 1)]
  apply mem_closedBall_of_sum_sq_le
  rw [Fin.sum_univ_four]
  nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

theorem volume_sep_lt_top {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    volume {v : Fin 4 → ℝ | v ∈ wedgeShell ∧ (v 0 + v 1) * (b * v 0 + a * v 1) ≤ 0} < ⊤ :=
  (Metric.isBounded_closedBall.subset (sep_subset_closedBall ha hb)).measure_lt_top

/-- `W(e^{−2r}, 1)` separates `diag(1, 1)` from `diag(eʳ, e⁻ʳ)`. -/
theorem wedge_sep_of_nonneg_side (r : ℝ) {v : Fin 4 → ℝ}
    (hv : v ∈ wedge (Real.exp (-(2 * r))) 1) :
    (v 0 + v 1) * (Real.exp (-r) * v 0 + Real.exp r * v 1) < 0 := by
  obtain ⟨-, h1, h2⟩ := hv
  have hA : 0 < v 0 * (v 0 + v 1) := by linarith
  have e : v 0 * (Real.exp (-r) * v 0 + Real.exp r * v 1) =
      Real.exp r * (Real.exp (-(2 * r)) * v 0 ^ 2 + v 0 * v 1) := by
    rw [show -r = r + -(2 * r) by ring, Real.exp_add]
    ring
  have hB : v 0 * (Real.exp (-r) * v 0 + Real.exp r * v 1) < 0 := by
    rw [e]
    exact mul_neg_of_pos_of_neg (Real.exp_pos r) (by linarith)
  have hprod : (v 0 * (v 0 + v 1)) * (v 0 * (Real.exp (-r) * v 0 + Real.exp r * v 1)) < 0 :=
    mul_neg_of_pos_of_neg hA hB
  have e2 : (v 0 * (v 0 + v 1)) * (v 0 * (Real.exp (-r) * v 0 + Real.exp r * v 1)) =
      v 0 ^ 2 * ((v 0 + v 1) * (Real.exp (-r) * v 0 + Real.exp r * v 1)) := by ring
  rw [e2] at hprod
  exact neg_of_mul_neg_right hprod (sq_nonneg _)

/-- `W(1, e^{−2r})` separates `diag(1, 1)` from `diag(eʳ, e⁻ʳ)`. -/
theorem wedge_sep_of_nonpos_side (r : ℝ) {v : Fin 4 → ℝ}
    (hv : v ∈ wedge 1 (Real.exp (-(2 * r)))) :
    (v 0 + v 1) * (Real.exp (-r) * v 0 + Real.exp r * v 1) < 0 := by
  obtain ⟨-, h1, h2⟩ := hv
  have hA : v 0 * (v 0 + v 1) < 0 := by linarith
  have e : v 0 * (Real.exp (-r) * v 0 + Real.exp r * v 1) =
      Real.exp r * (Real.exp (-(2 * r)) * v 0 ^ 2 + v 0 * v 1) := by
    rw [show -r = r + -(2 * r) by ring, Real.exp_add]
    ring
  have hB : 0 < v 0 * (Real.exp (-r) * v 0 + Real.exp r * v 1) := by
    rw [e]
    exact mul_pos (Real.exp_pos r) (by linarith)
  have hprod : (v 0 * (v 0 + v 1)) * (v 0 * (Real.exp (-r) * v 0 + Real.exp r * v 1)) < 0 :=
    mul_neg_of_neg_of_pos hA hB
  have e2 : (v 0 * (v 0 + v 1)) * (v 0 * (Real.exp (-r) * v 0 + Real.exp r * v 1)) =
      v 0 ^ 2 * ((v 0 + v 1) * (Real.exp (-r) * v 0 + Real.exp r * v 1)) := by ring
  rw [e2] at hprod
  exact neg_of_mul_neg_right hprod (sq_nonneg _)

/-- **The separating shell vectors have volume at least `2|r|·φ(1)`.** -/
theorem volume_sep_ge (r : ℝ) :
    2 * |r| * wedgePhi 1 ≤
      (volume {v : Fin 4 → ℝ | v ∈ wedgeShell ∧
        (v 0 + v 1) * (Real.exp (-r) * v 0 + Real.exp r * v 1) < 0}).toReal := by
  have hfin : volume {v : Fin 4 → ℝ | v ∈ wedgeShell ∧
      (v 0 + v 1) * (Real.exp (-r) * v 0 + Real.exp r * v 1) < 0} ≠ ⊤ := by
    refine ne_top_of_le_ne_top (volume_sep_lt_top (Real.exp_pos r) (Real.exp_pos (-r))).ne
      (measure_mono ?_)
    rintro v ⟨hv, h⟩
    exact ⟨hv, h.le⟩
  rcases le_total 0 r with hr | hr
  · have hW : volume (wedge (Real.exp (-(2 * r))) 1) = volume (wedge 1 (Real.exp (2 * r))) := by
      have h := volume_wedge_scale r (Real.exp (-(2 * r))) 1
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at h
      exact h.symm
    have hsub : wedge (Real.exp (-(2 * r))) 1 ⊆ {v : Fin 4 → ℝ | v ∈ wedgeShell ∧
        (v 0 + v 1) * (Real.exp (-r) * v 0 + Real.exp r * v 1) < 0} :=
      fun v hv ↦ ⟨hv.1, wedge_sep_of_nonneg_side r hv⟩
    have hphi : wedgePhi (2 * r) = 2 * |r| * wedgePhi 1 := by
      rw [wedgePhi_eq_mul (by linarith), abs_of_nonneg hr]
    rw [← hphi]
    unfold wedgePhi
    rw [← hW]
    exact ENNReal.toReal_mono hfin (measure_mono hsub)
  · have hsub : wedge 1 (Real.exp (-(2 * r))) ⊆ {v : Fin 4 → ℝ | v ∈ wedgeShell ∧
        (v 0 + v 1) * (Real.exp (-r) * v 0 + Real.exp r * v 1) < 0} :=
      fun v hv ↦ ⟨hv.1, wedge_sep_of_nonpos_side r hv⟩
    have hphi : wedgePhi (-(2 * r)) = 2 * |r| * wedgePhi 1 := by
      rw [wedgePhi_eq_mul (by linarith), abs_of_nonpos hr]
      ring
    rw [← hphi]
    exact ENNReal.toReal_mono hfin (measure_mono hsub)

end

end Wedge
end GHW
end GroupApproximation

open GroupApproximation.GHW.Wedge

#audit_axioms eq_mul_of_additive_monotoneOn
#audit_axioms volume_wedge_pos
#audit_axioms volume_wedge_lt_top
#audit_axioms measurePreserving_hypScale
#audit_axioms volume_wedge_scale
#audit_axioms volume_wedge_add
#audit_axioms wedgePhi_eq_mul
#audit_axioms wedgePhi_one_pos
#audit_axioms volume_sep_lt_top
#audit_axioms volume_sep_ge
