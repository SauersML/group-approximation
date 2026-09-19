import GroupApproximation.AlgTop.ComplexProjectiveHyperplane

/-!
# Pushing `ℂP^{d+1}` off its base point onto the hyperplane

Mayer–Vietoris for `ℂP^{d+1}` uses the open cover by the affine chart
`CPn.chartSet (d+1)` (contractible, `CPn.chartHomeo`) and the complement of the base
point. This file supplies the second half: an explicit deformation of
`ℂP^{d+1} ∖ {basePoint}` onto the hyperplane `ℂP^d`, done entirely inside the projection
model.

## The construction

Scale the first homogeneous coordinate down to `0`. On projections, scaling the vector
`z` by the real diagonal `δ t = (1-t, 1, …, 1)` and renormalizing is

```text
(scale t x) a b = δ t a * x a b * δ t b / τ t x,     τ t x = ∑ c, (δ t c)² * x c c.
```

Two facts make this work, and both are consequences of the rank-one identity
`CPn.minor` alone — no rank theorem, no spectral theorem, no square roots:

* `CPn.weighted_sum` : `∑ c, δ c * (x a c * x c b) = (∑ c, δ c * x c c) * x a b`
  for **any** weights `δ`. With `δ c = (δ t c)²` this is exactly the idempotent law for
  the scaled matrix, and with `a = b` it also computes its trace.
* `CPn.rad_eq_one_iff` : `∑ k ‖x k 0‖² = 1` iff `x` is the base point. So away from the
  base point `τ t x ≥ 1 - rad x > 0` for EVERY real `t` — `(1-t)²` is a square, so the
  interval `[0,1]` is never needed for this — and the renormalization never divides by zero.

## Main results

* `CPn.weighted_sum` — the weighted idempotent identity;
* `CPn.rad`, `CPn.rad_le_one`, `CPn.rad_eq_one_iff` — the `(0,0)` entry as a real number
  in `[0,1]`, equal to `1` exactly at the base point;
* `CPn.scale : unitInterval × ↥(CPn.punctured d) → CP (d+1)` — the deformation, with
  `CPn.scale_zero` (`t = 0` is the identity), `CPn.scale_one_entry_zero_zero` (`t = 1`
  lands in the hyperplane `CPn.range_incl`) and `CPn.scale_of_entry_zero_zero_eq_zero`
  (every `t` fixes the hyperplane pointwise);
* `CPn.continuous_scale` — joint continuity in `(t, x)`.
-/

noncomputable section

namespace GroupApproximation.AlgTop

open Matrix
open GroupApproximation.STW59
open scoped unitInterval

namespace CPn

variable {d : ℕ}

/-! ## 1. Some diagonal entry is nonzero -/

theorem exists_diag_ne_zero (x : CP d) : ∃ j, entry x j j ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have h := trace_coe x
  simp only [Matrix.trace, Matrix.diag_apply] at h
  rw [Finset.sum_eq_zero fun j (_ : j ∈ Finset.univ) => hcon j] at h
  exact zero_ne_one h

/-! ## 2. The weighted idempotent identity -/

/-- **Weighted idempotency.** For a rank-one projection and *arbitrary* weights `δ`,

```text
∑ c, δ c * (x a c * x c b) = (∑ c, δ c * x c c) * x a b.
```

Taking `δ = 1` recovers the idempotent law; taking `δ c` to be `(1-t)²` or `1` according
to whether `c = 0` is what makes the deformation below land back in `ℂP^{d+1}`. The proof
is the rank-one identity `CPn.minor` used four times, then cancellation of a nonzero
diagonal entry. -/
theorem weighted_sum (x : CP d) (δ : Fin (d + 1) → ℂ) (a b : Fin (d + 1)) :
    (∑ c, δ c * (entry x a c * entry x c b)) = (∑ c, δ c * entry x c c) * entry x a b := by
  obtain ⟨j, hj⟩ := exists_diag_ne_zero x
  have key : ∀ c, entry x j j * entry x j j * (entry x a c * entry x c b)
      = entry x j j * entry x j j * (entry x c c * entry x a b) := by
    intro c
    have h1 : entry x j j * entry x a c = entry x a j * entry x j c := (entry_minor x a c j).symm
    have h2 : entry x j j * entry x c b = entry x c j * entry x j b := (entry_minor x c b j).symm
    have h3 : entry x j c * entry x c j = entry x c c * entry x j j := entry_minor x j j c
    have h4 : entry x a j * entry x j b = entry x j j * entry x a b := entry_minor x a b j
    calc entry x j j * entry x j j * (entry x a c * entry x c b)
        = (entry x j j * entry x a c) * (entry x j j * entry x c b) := by ring
      _ = (entry x a j * entry x j c) * (entry x c j * entry x j b) := by rw [h1, h2]
      _ = (entry x a j * entry x j b) * (entry x j c * entry x c j) := by ring
      _ = (entry x j j * entry x a b) * (entry x c c * entry x j j) := by rw [h3, h4]
      _ = entry x j j * entry x j j * (entry x c c * entry x a b) := by ring
  have hmul : ∀ c, entry x j j * entry x j j * (δ c * (entry x a c * entry x c b))
      = entry x j j * entry x j j * (δ c * entry x c c * entry x a b) := by
    intro c
    linear_combination δ c * key c
  have hL : entry x j j * entry x j j * (∑ c, δ c * (entry x a c * entry x c b))
      = ∑ c, entry x j j * entry x j j * (δ c * (entry x a c * entry x c b)) :=
    Finset.mul_sum _ _ _
  have hR : entry x j j * entry x j j * ((∑ c, δ c * entry x c c) * entry x a b)
      = ∑ c, entry x j j * entry x j j * (δ c * entry x c c * entry x a b) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  refine mul_left_cancel₀ (mul_ne_zero hj hj) ?_
  rw [hL, hR]
  exact Finset.sum_congr rfl fun c _ => hmul c

/-! ## 3. The `(0,0)` entry as a real number -/

/-- The real diagonal entries of a rank-one projection: `x a a = ∑ k ‖x k a‖²`. -/
def diagR (x : CP d) (a : Fin (d + 1)) : ℝ := ∑ k, ‖entry x k a‖ ^ 2

theorem diagR_nonneg (x : CP d) (a : Fin (d + 1)) : 0 ≤ diagR x a :=
  Finset.sum_nonneg fun k _ => by positivity

theorem entry_diag_eq_diagR (x : CP d) (a : Fin (d + 1)) :
    entry x a a = ((diagR x a : ℝ) : ℂ) := entry_diag x a

theorem sum_diagR (x : CP d) : (∑ a, diagR x a) = 1 :=
  proj_sum_sq_eq_one (isStarProjection_coe x) (trace_coe x)

theorem diagR_le_one (x : CP d) (a : Fin (d + 1)) : diagR x a ≤ 1 := by
  rw [← sum_diagR x]
  exact Finset.single_le_sum (fun c _ => diagR_nonneg x c) (Finset.mem_univ a)

/-- The `(0,0)` entry of a point of `ℂP^d`, as a real number in `[0,1]`. -/
def rad (x : CP d) : ℝ := diagR x 0

theorem rad_nonneg (x : CP d) : 0 ≤ rad x := diagR_nonneg x 0

theorem rad_le_one (x : CP d) : rad x ≤ 1 := diagR_le_one x 0

theorem entry_zero_zero_eq_rad (x : CP d) : entry x 0 0 = ((rad x : ℝ) : ℂ) :=
  entry_diag_eq_diagR x 0

/-- If `rad x = 1` then every other diagonal entry vanishes. -/
theorem diagR_eq_zero_of_rad_eq_one {x : CP d} (h : rad x = 1) {a : Fin (d + 1)}
    (ha : a ≠ 0) : diagR x a = 0 := by
  classical
  have hpair : diagR x 0 + diagR x a ≤ ∑ c, diagR x c := by
    rw [← Finset.sum_pair (Ne.symm ha)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun c _ _ => diagR_nonneg x c
  rw [sum_diagR x] at hpair
  have h0 : diagR x 0 = 1 := h
  rw [h0] at hpair
  exact le_antisymm (by linarith) (diagR_nonneg x a)

/-- **The base point is the only point of `ℂP^d` with `rad = 1`.** -/
theorem rad_eq_one_iff {x : CP d} : rad x = 1 ↔ x = basePoint d := by
  constructor
  · intro h
    have hzero : ∀ a : Fin (d + 1), a ≠ 0 → entry x a a = 0 := by
      intro a ha
      rw [entry_diag_eq_diagR x a, diagR_eq_zero_of_rad_eq_one h ha, Complex.ofReal_zero]
    have h00 : entry x 0 0 = 1 := by
      rw [entry_zero_zero_eq_rad, h, Complex.ofReal_one]
    refine ext fun a b => ?_
    rw [basePoint_entry]
    by_cases ha : a = 0
    · subst ha
      by_cases hb : b = 0
      · subst hb
        rw [h00, baseVec_zero]
        simp
      · rw [entry_col_eq_zero x (hzero b hb) 0, baseVec_apply_of_ne hb]
        simp
    · rw [entry_row_eq_zero x (hzero a ha) b, baseVec_apply_of_ne ha]
      simp
  · rintro rfl
    have h : entry (basePoint d) 0 0 = ((rad (basePoint d) : ℝ) : ℂ) :=
      entry_zero_zero_eq_rad _
    rw [basePoint_entry_zero_zero] at h
    exact_mod_cast h.symm

theorem rad_lt_one {x : CP d} (hx : x ≠ basePoint d) : rad x < 1 :=
  lt_of_le_of_ne (rad_le_one x) fun h => hx (rad_eq_one_iff.mp h)

/-! ## 4. The scaling deformation -/

/-- `ℂP^{d+1}` with the base point removed. -/
def punctured (d : ℕ) : Set (CP (d + 1)) := {x | x ≠ basePoint (d + 1)}

theorem isOpen_punctured : IsOpen (punctured d) :=
  isOpen_compl_singleton

theorem mem_punctured {x : CP (d + 1)} : x ∈ punctured d ↔ x ≠ basePoint (d + 1) := Iff.rfl

/-- The real diagonal `(1-t, 1, …, 1)`. -/
def scaleVec (t : ℝ) : Fin (d + 2) → ℝ := Fin.cons (1 - t) 1

@[simp] theorem scaleVec_zero (t : ℝ) : scaleVec (d := d) t 0 = 1 - t := by
  simp [scaleVec]

@[simp] theorem scaleVec_succ (t : ℝ) (i : Fin (d + 1)) : scaleVec (d := d) t i.succ = 1 := by
  simp [scaleVec]

/-- The normalizing trace `∑ c, (scaleVec t c)² * x c c`, as a real number. -/
def scaleTrace (t : ℝ) (x : CP (d + 1)) : ℝ := (1 - t) ^ 2 * rad x + (1 - rad x)

theorem scaleTrace_pos {t : ℝ} {x : CP (d + 1)}
    (hx : x ≠ basePoint (d + 1)) : 0 < scaleTrace t x := by
  have h1 : rad x < 1 := rad_lt_one hx
  have h2 : (0:ℝ) ≤ (1 - t) ^ 2 * rad x := mul_nonneg (sq_nonneg _) (rad_nonneg x)
  simp only [scaleTrace]
  linarith

theorem scaleTrace_ne_zero {t : ℝ} {x : CP (d + 1)}
    (hx : x ≠ basePoint (d + 1)) : ((scaleTrace t x : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (scaleTrace_pos hx).ne'

/-- The identity that makes the renormalization work: the weighted trace of `x` with
weights `(scaleVec t c)²` is `scaleTrace t x`. -/
theorem sum_scaleVec_sq_diag (t : ℝ) (x : CP (d + 1)) :
    (∑ c, ((scaleVec (d := d) t c : ℝ) : ℂ) ^ 2 * entry x c c)
      = ((scaleTrace t x : ℝ) : ℂ) := by
  have htrace : entry x 0 0 + ∑ i : Fin (d + 1), entry x i.succ i.succ = 1 := by
    have h := trace_coe x
    simp only [Matrix.trace, Matrix.diag_apply] at h
    rw [Fin.sum_univ_succ] at h
    exact h
  have hsum : (∑ i : Fin (d + 1), entry x i.succ i.succ) = 1 - ((rad x : ℝ) : ℂ) := by
    rw [← entry_zero_zero_eq_rad]
    linear_combination htrace
  rw [Fin.sum_univ_succ]
  have htail : (∑ i : Fin (d + 1), ((scaleVec (d := d) t i.succ : ℝ) : ℂ) ^ 2
      * entry x i.succ i.succ) = ∑ i : Fin (d + 1), entry x i.succ i.succ := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [scaleVec_succ]
    norm_num
  rw [htail, hsum, scaleVec_zero, entry_zero_zero_eq_rad]
  simp only [scaleTrace]
  push_cast
  ring

/-- The scaled matrix. -/
def scaleMat (t : ℝ) (x : CP (d + 1)) : Matrix (Fin (d + 2)) (Fin (d + 2)) ℂ :=
  Matrix.of fun a b =>
    ((scaleVec (d := d) t a : ℝ) : ℂ) * entry x a b * ((scaleVec (d := d) t b : ℝ) : ℂ)
      / ((scaleTrace t x : ℝ) : ℂ)

@[simp] theorem scaleMat_apply (t : ℝ) (x : CP (d + 1)) (a b : Fin (d + 2)) :
    scaleMat t x a b =
      ((scaleVec (d := d) t a : ℝ) : ℂ) * entry x a b * ((scaleVec (d := d) t b : ℝ) : ℂ)
        / ((scaleTrace t x : ℝ) : ℂ) := rfl

theorem scaleMat_mem {t : ℝ} {x : CP (d + 1)}
    (hx : x ≠ basePoint (d + 1)) : scaleMat t x ∈ cpSet (d + 1) := by
  have hτ : ((scaleTrace t x : ℝ) : ℂ) ≠ 0 := scaleTrace_ne_zero hx
  refine ⟨?_, ?_, ?_⟩
  · refine Matrix.ext fun a b => ?_
    rw [Matrix.conjTranspose_apply, scaleMat_apply, scaleMat_apply]
    simp only [Complex.star_def, map_div₀, map_mul, Complex.conj_ofReal, entry_conj]
    ring
  · refine Matrix.ext fun a b => ?_
    rw [Matrix.mul_apply]
    have hterm : ∀ c, scaleMat (d := d) t x a c * scaleMat (d := d) t x c b
        = (((scaleVec (d := d) t a : ℝ) : ℂ) * ((scaleVec (d := d) t b : ℝ) : ℂ)
            / (((scaleTrace t x : ℝ) : ℂ) * ((scaleTrace t x : ℝ) : ℂ)))
          * (((scaleVec (d := d) t c : ℝ) : ℂ) ^ 2 * (entry x a c * entry x c b)) := by
      intro c
      rw [scaleMat_apply, scaleMat_apply]
      field_simp
      ring
    rw [Finset.sum_congr rfl fun c _ => hterm c, ← Finset.mul_sum,
      weighted_sum x (fun c => ((scaleVec (d := d) t c : ℝ) : ℂ) ^ 2) a b,
      sum_scaleVec_sq_diag t x, scaleMat_apply]
    field_simp
    ring
  · simp only [Matrix.trace, Matrix.diag_apply]
    have hterm : ∀ a : Fin (d + 2), scaleMat (d := d) t x a a
        = (((scaleVec (d := d) t a : ℝ) : ℂ) ^ 2 * entry x a a)
            / ((scaleTrace t x : ℝ) : ℂ) := by
      intro a
      rw [scaleMat_apply]
      ring
    rw [Finset.sum_congr rfl fun a _ => hterm a, ← Finset.sum_div, sum_scaleVec_sq_diag t x]
    exact div_self hτ

/-- **The deformation.** `scale (t, x)` scales the first homogeneous coordinate of `x` by
`1 - t`; it is defined on all of `I × (ℂP^{d+1} ∖ {basePoint})`. -/
def scale (p : I × ↥(punctured d)) : CP (d + 1) :=
  ⟨scaleMat (p.1 : ℝ) (p.2 : CP (d + 1)), scaleMat_mem p.2.2⟩

@[simp] theorem scale_entry (p : I × ↥(punctured d)) (a b : Fin (d + 2)) :
    entry (scale p) a b = scaleMat (p.1 : ℝ) (p.2 : CP (d + 1)) a b := rfl

/-- At `t = 0` the deformation is the identity. -/
theorem scale_zero (x : ↥(punctured d)) : scale ((0 : I), x) = (x : CP (d + 1)) := by
  have h0 : ((0 : I) : ℝ) = 0 := rfl
  refine ext fun a b => ?_
  rw [scale_entry, scaleMat_apply, h0]
  have hτ : scaleTrace (0:ℝ) (x : CP (d + 1)) = 1 := by
    simp only [scaleTrace]
    ring
  have hv : ∀ c : Fin (d + 2), ((scaleVec (d := d) (0:ℝ) c : ℝ) : ℂ) = 1 := by
    intro c
    refine Fin.cases ?_ ?_ c
    · rw [scaleVec_zero]; norm_num
    · intro i; rw [scaleVec_succ]; norm_num
  rw [hv a, hv b, hτ]
  norm_num

/-- At `t = 1` the deformation lands in the hyperplane `CPn.range_incl`. -/
theorem scale_one_entry_zero_zero (x : ↥(punctured d)) :
    entry (scale ((1 : I), x)) 0 0 = 0 := by
  have h1 : ((1 : I) : ℝ) = 1 := rfl
  rw [scale_entry, scaleMat_apply, h1, scaleVec_zero]
  norm_num

theorem scale_one_mem_range_incl (x : ↥(punctured d)) :
    scale ((1 : I), x) ∈ Set.range (incl (d := d)) := by
  rw [range_incl]
  exact scale_one_entry_zero_zero x

/-- Every stage of the deformation fixes the hyperplane pointwise. -/
theorem scale_of_entry_zero_zero_eq_zero (p : I × ↥(punctured d))
    (h0 : entry (p.2 : CP (d + 1)) 0 0 = 0) : scale p = (p.2 : CP (d + 1)) := by
  have hrad : rad (p.2 : CP (d + 1)) = 0 := by
    have h := entry_zero_zero_eq_rad (p.2 : CP (d + 1))
    rw [h0] at h
    exact_mod_cast h.symm
  have hτ : scaleTrace (p.1 : ℝ) (p.2 : CP (d + 1)) = 1 := by
    simp only [scaleTrace, hrad]
    ring
  refine ext fun a b => ?_
  rw [scale_entry, scaleMat_apply, hτ]
  refine Fin.cases ?_ ?_ a
  · rw [entry_row_eq_zero (p.2 : CP (d + 1)) h0 b]
    norm_num
  · intro i
    refine Fin.cases ?_ ?_ b
    · rw [entry_col_eq_zero (p.2 : CP (d + 1)) h0 i.succ]
      norm_num
    · intro j
      rw [scaleVec_succ, scaleVec_succ]
      norm_num

/-! ## 5. Continuity -/

theorem continuous_diagR (a : Fin (d + 1)) : Continuous fun x : CP d => diagR x a := by
  show Continuous fun x : CP d => ∑ k, ‖entry x k a‖ ^ 2
  exact continuous_finsetSum _ fun k _ => ((continuous_entry k a).norm).pow 2

theorem continuous_rad : Continuous (rad (d := d)) := continuous_diagR 0

theorem continuous_scaleVec (a : Fin (d + 2)) :
    Continuous fun t : ℝ => scaleVec (d := d) t a := by
  refine Fin.cases ?_ ?_ a
  · simpa only [scaleVec_zero] using continuous_const.sub continuous_id
  · intro i
    simpa only [scaleVec_succ] using continuous_const

theorem continuous_scaleTrace :
    Continuous fun p : ℝ × CP (d + 1) => scaleTrace p.1 p.2 := by
  simp only [scaleTrace]
  exact (((continuous_const.sub continuous_fst).pow 2).mul
      (continuous_rad.comp continuous_snd)).add
    (continuous_const.sub (continuous_rad.comp continuous_snd))

theorem continuous_scale : Continuous (scale (d := d)) := by
  have hfst : Continuous fun p : I × ↥(punctured d) => ((p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hsnd : Continuous fun p : I × ↥(punctured d) => ((p.2 : CP (d + 1))) :=
    continuous_subtype_val.comp continuous_snd
  have hτ : Continuous fun p : I × ↥(punctured d) =>
      ((scaleTrace (p.1 : ℝ) (p.2 : CP (d + 1)) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_scaleTrace.comp (hfst.prodMk hsnd))
  apply Continuous.subtype_mk
  refine continuous_matrix fun a b => ?_
  refine Continuous.div ?_ hτ ?_
  · exact (((Complex.continuous_ofReal.comp
      ((continuous_scaleVec a).comp hfst)).mul
        ((continuous_entry a b).comp hsnd)).mul
          (Complex.continuous_ofReal.comp ((continuous_scaleVec b).comp hfst)))
  · intro p
    exact scaleTrace_ne_zero p.2.2

end CPn

end GroupApproximation.AlgTop
