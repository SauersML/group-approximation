import GroupApproximation.AlgTop.ComplexProjectiveBasic

/-!
# An explicit section of `(L*)^{⊕d}` over `ℂP^d` with exactly one zero

Lane `found-euler-class`, campaign target 3 (STW Problem LIX).

## What this file replaces

The counterexample manuscript
(`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`, §2)
needs, in the proof of Lemma 2, a section `σ` of `H` over `Y = ∏ⱼ ℂP^{dⱼ}` transverse
to zero, together with the *Chern-number* input

```text
|⟨c_m(H), [Y]⟩| = 1                                                    (2.1)
```

to conclude that the signed zero count of `σ` is `±1`.  Equation (2.1) is a
characteristic-class computation, and characteristic classes do not exist in Mathlib
at the campaign pin.

**This file removes (2.1) from the critical path.**  Taking `H` built from the *dual*
tautological line `L*` rather than from `L` — which changes nothing in the manuscript's
construction, in Lemma 3's `K`-theory, or in `⟨c_m, [Y]⟩ = ±1` — the section attached
to the coordinate linear forms becomes completely explicit, and the assertion "it has
exactly one zero" becomes **linear algebra about rank-one projections**.  No topology,
no cohomology, no characteristic class is used below.

## The section

Over the projection model `CP d` (a point *is* a rank-one projection `q`), the
tautological line is `L_q = range q` and a linear functional `ℓ` on `ℂ^{d+1}` restricts
to a section of `L*`.  Realizing `L* ≅ L̄` by the conjugate projection `q̄`, the section
attached to the `i`-th coordinate functional is

```text
s_i (q) = q̄ · eᵢ,     that is,     s_i (q) j = q i j,
```

the `i`-th **row** of `q` (`dualTautComponent_apply`); it really is a section of the
conjugate bundle (`dualTautComponent_isSection`), and it vanishes at `q` exactly when
the `i`-th row of `q` vanishes, i.e. when `ℓᵢ` kills `range q`.

Using the `d` functionals `ℓ₁, …, ℓ_d` (skipping `ℓ₀`) gives a section of `(L*)^{⊕d}`
whose zero locus is a single point.

## Main results

* `dualTautSection_eq_zero_iff` — the section vanishes at `x` **iff** `x` is the base
  point `[1 : 0 : ⋯ : 0]`.  Exactly one zero.
* `sectionChart_apply` — in the standard affine chart around the base point the section
  is `z ↦ (1 + ‖z‖²)⁻¹ z`, a *positive* scalar multiple of the identity of `ℂ^d`.
* `chartHomotopy_eq_zero_iff` — the straight-line homotopy from that map to the identity
  of `ℂ^d` has, at every time, the origin as its only zero.  This is the transversality
  input in the form a mod-2 local index consumes: no derivative, no orientation, no sign.
-/

noncomputable section

namespace GroupApproximation.AlgTop

open Matrix Complex
open scoped ComplexConjugate

variable {d : ℕ}

/-! ## 1. The section attached to a coordinate functional -/

/-- The section of the conjugate line bundle `L̄ ≅ L*` over `CP d` attached to the
`i`-th coordinate functional: at the rank-one projection `q` it is `q̄ · eᵢ`, i.e. the
`i`-th row of `q`. -/
def dualTautComponent (i : Fin (d + 1)) (x : CP d) : Fin (d + 1) → ℂ :=
  fun j => x.mat i j

@[simp]
theorem dualTautComponent_apply (i : Fin (d + 1)) (x : CP d) (j : Fin (d + 1)) :
    dualTautComponent i x j = x.mat i j := rfl

/-- `dualTautComponent i x` really is a section of the conjugate bundle: it is fixed by
the conjugate projection `q̄`.  (`conj (q j k) = q k j` by self-adjointness, so the sum
below is the `(i, j)` entry of `q * q = q`.) -/
theorem dualTautComponent_isSection (i : Fin (d + 1)) (x : CP d) (j : Fin (d + 1)) :
    (∑ k, conj (x.mat j k) * dualTautComponent i x k) = dualTautComponent i x j := by
  have hconj : ∀ k, conj (x.mat j k) = x.mat k j := fun k => x.prop.conj_entry j k
  have hrw : ∀ k, conj (x.mat j k) * dualTautComponent i x k = x.mat i k * x.mat k j := by
    intro k
    rw [hconj k, dualTautComponent_apply]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hrw k)]
  exact x.prop.sum_mul i j

/-- The section of `(L*)^{⊕d}` over `CP d` given by the `d` coordinate functionals
`ℓ₁, …, ℓ_d`.  Its `i`-th block is the `(i+1)`-st row of the projection. -/
def dualTautSection (x : CP d) : Fin d → Fin (d + 1) → ℂ :=
  fun i => dualTautComponent i.succ x

@[simp]
theorem dualTautSection_apply (x : CP d) (i : Fin d) (j : Fin (d + 1)) :
    dualTautSection x i j = x.mat i.succ j := rfl

/-! ## 2. The base point, entrywise -/

theorem basePoint_mat (d : ℕ) (a b : Fin (d + 1)) :
    (CP.basePoint d).mat a b = if a = 0 then (if b = 0 then 1 else 0) else 0 := by
  simp only [CP.basePoint, CP.ofVec_mat]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb]

theorem basePoint_mat_of_ne_zero {d : ℕ} {a : Fin (d + 1)} (ha : a ≠ 0) (b : Fin (d + 1)) :
    (CP.basePoint d).mat a b = 0 := by
  rw [basePoint_mat, if_neg ha]

/-! ## 3. Exactly one zero -/

/-- If every row of a rank-one projection other than the `0`-th vanishes, then so does
every column other than the `0`-th: the matrix is self-adjoint. -/
theorem col_eq_zero_of_rows_eq_zero {x : CP d}
    (h : ∀ a : Fin (d + 1), a ≠ 0 → ∀ b, x.mat a b = 0)
    (a b : Fin (d + 1)) (hb : b ≠ 0) : x.mat a b = 0 := by
  have h1 : conj (x.mat b a) = x.mat a b := x.prop.conj_entry b a
  rw [← h1, h b hb a, map_zero]

/-- **Exactly one zero.**  The section `dualTautSection` of `(L*)^{⊕d}` over `ℂP^d`
vanishes at `x` if and only if `x` is the base point `[1 : 0 : ⋯ : 0]`.

This is the manuscript's `|⟨c_m(H), [Y]⟩| = 1` for a single factor, proved without any
characteristic class: vanishing of the section says that the last `d` rows of the
projection are zero, self-adjointness then kills the last `d` columns, and the trace
condition forces the surviving entry to be `1`. -/
theorem dualTautSection_eq_zero_iff (x : CP d) :
    (∀ i j, dualTautSection x i j = 0) ↔ x = CP.basePoint d := by
  constructor
  · intro h
    -- Every row other than the `0`-th vanishes.
    have hrow : ∀ a : Fin (d + 1), a ≠ 0 → ∀ b, x.mat a b = 0 := by
      intro a ha b
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq_of_ne_zero ha
      simpa using h i b
    -- Hence every entry off the `(0, 0)` slot vanishes.
    have hoff : ∀ a b : Fin (d + 1), ¬ (a = 0 ∧ b = 0) → x.mat a b = 0 := by
      intro a b hab
      by_cases ha : a = 0
      · have hb : b ≠ 0 := fun hb => hab ⟨ha, hb⟩
        exact col_eq_zero_of_rows_eq_zero hrow a b hb
      · exact hrow a ha b
    -- The trace condition pins the surviving entry.
    have htr : x.mat 0 0 = 1 := by
      have h1 : x.mat.trace = 1 := x.prop.trace_eq
      rw [Matrix.trace] at h1
      simp only [Matrix.diag_apply] at h1
      rw [Finset.sum_eq_single (0 : Fin (d + 1))] at h1
      · exact h1
      · intro b _ hb
        exact hoff b b (fun hcon => hb hcon.1)
      · intro hcon
        exact absurd (Finset.mem_univ (0 : Fin (d + 1))) hcon
    -- Compare with the base point entrywise.
    refine CP.ext_iff'.mpr (fun a b => ?_)
    rw [basePoint_mat]
    by_cases ha : a = 0
    · by_cases hb : b = 0
      · rw [if_pos ha, if_pos hb, ha, hb]; exact htr
      · rw [if_pos ha, if_neg hb]
        exact hoff a b (fun hcon => hb hcon.2)
    · rw [if_neg ha]
      exact hoff a b (fun hcon => ha hcon.1)
  · intro h i j
    rw [dualTautSection_apply, h]
    exact basePoint_mat_of_ne_zero (Fin.exists_succ_eq.mp ⟨i, rfl⟩) j

/-- The zero locus of the section is the singleton `{basePoint}`. -/
theorem dualTautSection_zeroLocus (d : ℕ) :
    {x : CP d | ∀ i j, dualTautSection x i j = 0} = {CP.basePoint d} := by
  ext x
  simpa using dualTautSection_eq_zero_iff x

/-! ## 4. The section in the standard affine chart -/

/-- `1 + ‖z‖²`, the normalizing weight of the affine chart. -/
def chartNorm (z : Fin d → ℂ) : ℝ := 1 + ∑ b, Complex.normSq (z b)

theorem one_le_chartNorm (z : Fin d → ℂ) : 1 ≤ chartNorm z := by
  have : (0 : ℝ) ≤ ∑ b, Complex.normSq (z b) :=
    Finset.sum_nonneg fun b _ => Complex.normSq_nonneg (z b)
  simpa [chartNorm] using this

theorem chartNorm_pos (z : Fin d → ℂ) : 0 < chartNorm z :=
  lt_of_lt_of_le zero_lt_one (one_le_chartNorm z)

theorem chartNorm_ne_zero (z : Fin d → ℂ) : chartNorm z ≠ 0 := ne_of_gt (chartNorm_pos z)

/-- The normalized lift `(1, z) / √(1 + ‖z‖²)` of a chart coordinate. -/
def chartVec (z : Fin d → ℂ) : Fin (d + 1) → ℂ :=
  fun a => ((Real.sqrt (chartNorm z))⁻¹ : ℝ) * (Fin.cons 1 z : Fin (d + 1) → ℂ) a

theorem chartVec_apply (z : Fin d → ℂ) (a : Fin (d + 1)) :
    chartVec z a = ((Real.sqrt (chartNorm z))⁻¹ : ℝ) * (Fin.cons 1 z : Fin (d + 1) → ℂ) a :=
  rfl

theorem inv_sqrt_mul_inv_sqrt (z : Fin d → ℂ) :
    (Real.sqrt (chartNorm z))⁻¹ * (Real.sqrt (chartNorm z))⁻¹ = (chartNorm z)⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt (chartNorm_pos z).le]

theorem sum_normSq_chartVec (z : Fin d → ℂ) :
    (∑ a, Complex.normSq (chartVec z a)) = 1 := by
  have hstep : ∀ a : Fin (d + 1), Complex.normSq (chartVec z a)
      = (chartNorm z)⁻¹ * Complex.normSq ((Fin.cons 1 z : Fin (d + 1) → ℂ) a) := by
    intro a
    rw [chartVec_apply, Complex.normSq_mul, Complex.normSq_ofReal, inv_sqrt_mul_inv_sqrt]
  rw [Finset.sum_congr rfl (fun a _ => hstep a), ← Finset.mul_sum]
  have hsum : (∑ a, Complex.normSq ((Fin.cons 1 z : Fin (d + 1) → ℂ) a)) = chartNorm z := by
    rw [Fin.sum_univ_succ]
    simp [chartNorm]
  rw [hsum, inv_mul_cancel₀ (chartNorm_ne_zero z)]

/-- The standard affine chart of `ℂP^d` around the base point, in the projection model:
`z ↦ ` the rank-one projection onto the line spanned by `(1, z)`. -/
def chart (z : Fin d → ℂ) : CP d := CP.ofVec (chartVec z) (sum_normSq_chartVec z)

@[simp]
theorem chart_mat (z : Fin d → ℂ) (a b : Fin (d + 1)) :
    (chart z).mat a b = chartVec z a * conj (chartVec z b) :=
  CP.ofVec_mat _ _ a b

theorem chart_zero (d : ℕ) : chart (0 : Fin d → ℂ) = CP.basePoint d := by
  refine (dualTautSection_eq_zero_iff _).mp (fun i j => ?_)
  rw [dualTautSection_apply, chart_mat]
  simp [chartVec_apply]

/-- **The section in the chart.**  Along the affine chart around its zero, the section
is `z ↦ (1 + ‖z‖²)⁻¹ z`: a *positive real* multiple of the identity of `ℂ^d`.  (Only the
`0`-th coordinate of each block is recorded; that is the coordinate in which the
trivialization of `L*` over the chart is written.) -/
def sectionChart (z : Fin d → ℂ) : Fin d → ℂ := fun i => dualTautSection (chart z) i 0

theorem sectionChart_apply (z : Fin d → ℂ) (i : Fin d) :
    sectionChart z i = ((chartNorm z)⁻¹ : ℝ) * z i := by
  have hc : ((Real.sqrt (chartNorm z))⁻¹ : ℂ) * ((Real.sqrt (chartNorm z))⁻¹ : ℂ)
      = ((chartNorm z)⁻¹ : ℂ) := by
    rw [← Complex.ofReal_mul, inv_sqrt_mul_inv_sqrt]
  simp only [sectionChart, dualTautSection_apply, chart_mat, chartVec_apply, Fin.cons_succ,
    Fin.cons_zero, map_mul, Complex.conj_ofReal, map_one, mul_one]
  have hre : ((Real.sqrt (chartNorm z))⁻¹ : ℂ) * z i * ((Real.sqrt (chartNorm z))⁻¹ : ℂ)
      = (((Real.sqrt (chartNorm z))⁻¹ : ℂ) * ((Real.sqrt (chartNorm z))⁻¹ : ℂ)) * z i := by
    ring
  rw [hre, hc]

theorem sectionChart_eq_zero_iff (z : Fin d → ℂ) :
    (∀ i, sectionChart z i = 0) ↔ z = 0 := by
  constructor
  · intro h
    funext i
    have hi := h i
    rw [sectionChart_apply] at hi
    have hne : ((chartNorm z)⁻¹ : ℂ) ≠ 0 := by
      simpa using inv_ne_zero (chartNorm_ne_zero z)
    simpa using (mul_eq_zero.mp hi).resolve_left hne
  · intro h i
    rw [sectionChart_apply, h]
    simp

/-! ## 5. Transversality, in the form a mod-2 index consumes -/

/-- The straight-line homotopy in `ℂ^d` from the identity (`s = 0`) to the chart form of
the section (`s = 1`). -/
def chartHomotopy (s : ℝ) (z : Fin d → ℂ) : Fin d → ℂ :=
  fun i => (((1 - s) + s * (chartNorm z)⁻¹ : ℝ) : ℂ) * z i

theorem chartHomotopy_zero (z : Fin d → ℂ) : chartHomotopy 0 z = z := by
  funext i
  simp [chartHomotopy]

theorem chartHomotopy_one (z : Fin d → ℂ) : chartHomotopy 1 z = sectionChart z := by
  funext i
  rw [sectionChart_apply]
  simp [chartHomotopy]

/-- The homotopy coefficient is strictly positive at every time of the interval. -/
theorem chartHomotopy_coeff_pos {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (z : Fin d → ℂ) :
    0 < (1 - s) + s * (chartNorm z)⁻¹ := by
  have hinv : 0 < (chartNorm z)⁻¹ := inv_pos.mpr (chartNorm_pos z)
  rcases eq_or_lt_of_le hs0 with h | h
  · rw [← h]
    norm_num
  · have h1 : 0 ≤ 1 - s := by linarith
    have h2 : 0 < s * (chartNorm z)⁻¹ := mul_pos h hinv
    linarith

/-- **Transversality of the zero, mod-2 form.**  At every time `s ∈ [0, 1]` the homotopy
from the identity of `ℂ^d` to the chart form of the section has the origin as its only
zero.  So the section's zero is isolated and its local index equals that of the identity;
in particular it is odd.

No derivative, no determinant, no orientation of `ℂ^d` or of `ℂP^d` enters — which is the
whole point of running the campaign's obstruction mod `2`. -/
theorem chartHomotopy_eq_zero_iff {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (z : Fin d → ℂ) :
    (∀ i, chartHomotopy s z i = 0) ↔ z = 0 := by
  have hpos := chartHomotopy_coeff_pos hs0 hs1 z
  have hne : ((((1 - s) + s * (chartNorm z)⁻¹ : ℝ)) : ℂ) ≠ 0 := by
    simpa using ne_of_gt hpos
  constructor
  · intro h
    funext i
    have hi := h i
    rw [chartHomotopy] at hi
    exact (mul_eq_zero.mp hi).resolve_left hne
  · intro h i
    rw [chartHomotopy, h]
    simp

end GroupApproximation.AlgTop
