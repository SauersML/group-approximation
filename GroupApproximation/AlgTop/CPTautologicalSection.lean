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

**This file removes (2.1) from the critical path.**  The section attached to the
coordinate linear forms is completely explicit, and the assertion "it has exactly one
zero" becomes **linear algebra about rank-one projections**.  No topology, no
cohomology, no characteristic class is used below.

The bundle used here is the *dual* tautological line `L*` (equivalently the conjugate
`L̄`).  That is a convenience of presentation, not a change to the manuscript: the same
one-zero theorem holds for `L` itself, via the section `σ_a (z) = z · a` cut out by a
constant vector, so `H = ⊕ⱼ Lⱼ^{⊕dⱼ}` needs no amendment.  The two differ only in the
*sign* of the local index — the chart model here is the identity of `ℂ^d`, the chart
model for `L` is componentwise conjugation, of real determinant `(-1)^d` — and mod `2`,
which is all the parity contradiction needs, they agree.

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
* `tautChartHomotopy_eq_zero_iff` — the straight-line homotopy from that map to the
  identity of `ℂ^d` has, at every time, the origin as its only zero.  This is the
  transversality input in the form a mod-2 local index consumes: no derivative, no
  orientation, no sign.
-/

noncomputable section

namespace GroupApproximation.AlgTop

open Matrix
open GroupApproximation.STW59

namespace CPn

variable {d : ℕ}

/-! ## 1. The section attached to a coordinate functional -/

/-- The section of the conjugate line bundle `L̄ ≅ L*` over `CP d` attached to the
`i`-th coordinate functional: at the rank-one projection `q` it is `q̄ · eᵢ`, i.e. the
`i`-th row of `q`. -/
def dualTautComponent (i : Fin (d + 1)) (x : CP d) : Fin (d + 1) → ℂ :=
  fun j => entry x i j

@[simp]
theorem dualTautComponent_apply (i : Fin (d + 1)) (x : CP d) (j : Fin (d + 1)) :
    dualTautComponent i x j = entry x i j := rfl

/-- `dualTautComponent i x` really is a section of the conjugate bundle: it is fixed by
the conjugate projection `q̄`.  (`star (q j k) = q k j` by self-adjointness, so the sum
below is the `(i, j)` entry of `q * q = q`.) -/
theorem dualTautComponent_isSection (i : Fin (d + 1)) (x : CP d) (j : Fin (d + 1)) :
    (∑ k, star (entry x j k) * dualTautComponent i x k) = dualTautComponent i x j := by
  have hrw : ∀ k, star (entry x j k) * dualTautComponent i x k = entry x i k * entry x k j := by
    intro k
    have h1 : star (entry x j k) = entry x k j := (entry_symm x k j).symm
    rw [h1, dualTautComponent_apply]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hrw k)]
  exact entry_sum_mul x i j

/-- The section of `(L*)^{⊕d}` over `CP d` given by the `d` coordinate functionals
`ℓ₁, …, ℓ_d`.  Its `i`-th block is the `(i+1)`-st row of the projection. -/
def dualTautSection (x : CP d) : Fin d → Fin (d + 1) → ℂ :=
  fun i => dualTautComponent i.succ x

@[simp]
theorem dualTautSection_apply (x : CP d) (i : Fin d) (j : Fin (d + 1)) :
    dualTautSection x i j = entry x i.succ j := rfl

/-! ## 2. The base point, entrywise -/

theorem basePoint_entry_of_row_ne_zero {a : Fin (d + 1)} (ha : a ≠ 0) (b : Fin (d + 1)) :
    entry (basePoint d) a b = 0 := by
  rw [basePoint_entry, baseVec_apply_of_ne ha, zero_mul]

theorem basePoint_entry_of_col_ne_zero {b : Fin (d + 1)} (hb : b ≠ 0) (a : Fin (d + 1)) :
    entry (basePoint d) a b = 0 := by
  rw [basePoint_entry, baseVec_apply_of_ne hb, star_zero, mul_zero]

/-! ## 3. Exactly one zero -/

/-- If every row of a rank-one projection other than the `0`-th vanishes, then so does
every column other than the `0`-th: the matrix is self-adjoint. -/
theorem col_eq_zero_of_rows_eq_zero {x : CP d}
    (h : ∀ a : Fin (d + 1), a ≠ 0 → ∀ b, entry x a b = 0)
    (a b : Fin (d + 1)) (hb : b ≠ 0) : entry x a b = 0 := by
  rw [entry_symm x a b, h b hb a, star_zero]

/-- **Exactly one zero.**  The section `dualTautSection` of `(L*)^{⊕d}` over `ℂP^d`
vanishes at `x` if and only if `x` is the base point `[1 : 0 : ⋯ : 0]`.

This is the manuscript's `|⟨c_m(H), [Y]⟩| = 1` for a single factor, proved without any
characteristic class: vanishing of the section says that the rows other than the `0`-th
are zero, self-adjointness then kills the corresponding columns, and the trace condition
forces the surviving entry to be `1`. -/
theorem dualTautSection_eq_zero_iff (x : CP d) :
    (∀ i j, dualTautSection x i j = 0) ↔ x = basePoint d := by
  constructor
  · intro h
    -- Every row other than the `0`-th vanishes.
    have hrow : ∀ a : Fin (d + 1), a ≠ 0 → ∀ b, entry x a b = 0 := by
      intro a ha b
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq_of_ne_zero ha
      simpa using h i b
    -- Hence every entry off the `(0, 0)` slot vanishes.
    have hoff : ∀ a b : Fin (d + 1), ¬ (a = 0 ∧ b = 0) → entry x a b = 0 := by
      intro a b hab
      by_cases ha : a = 0
      · exact col_eq_zero_of_rows_eq_zero hrow a b (fun hb => hab ⟨ha, hb⟩)
      · exact hrow a ha b
    -- The trace condition pins the surviving entry.
    have htr : entry x 0 0 = 1 := by
      have h1 : (x : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).trace = 1 := trace_coe x
      rw [Matrix.trace] at h1
      simp only [Matrix.diag_apply] at h1
      rw [Finset.sum_eq_single (0 : Fin (d + 1))] at h1
      · exact h1
      · intro b _ hb
        exact hoff b b (fun hcon => hb hcon.1)
      · intro hcon
        exact absurd (Finset.mem_univ (0 : Fin (d + 1))) hcon
    -- Compare with the base point entrywise.
    refine ext (fun a b => ?_)
    by_cases ha : a = 0
    · by_cases hb : b = 0
      · subst ha
        subst hb
        rw [htr, basePoint_entry_zero_zero]
      · rw [hoff a b (fun hcon => hb hcon.2), basePoint_entry_of_col_ne_zero hb a]
    · rw [hoff a b (fun hcon => ha hcon.1), basePoint_entry_of_row_ne_zero ha b]
  · intro h i j
    rw [dualTautSection_apply, h]
    exact basePoint_entry_of_row_ne_zero (Fin.exists_succ_eq.mp ⟨i, rfl⟩) j

/-- The zero locus of the section is the singleton `{basePoint}`. -/
theorem dualTautSection_zeroLocus (d : ℕ) :
    {x : CP d | ∀ i j, dualTautSection x i j = 0} = {basePoint d} := by
  ext x
  simpa using dualTautSection_eq_zero_iff x

/-! ## 4. The section in the standard affine chart -/

/-- `1 + ‖z‖²`, the normalizing weight of the affine chart. -/
def tautChartNorm (z : Fin d → ℂ) : ℝ := 1 + ∑ b, ‖z b‖ ^ 2

theorem one_le_tautChartNorm (z : Fin d → ℂ) : 1 ≤ tautChartNorm z := by
  have h : (0 : ℝ) ≤ ∑ b, ‖z b‖ ^ 2 :=
    Finset.sum_nonneg fun b _ => sq_nonneg (‖z b‖)
  simpa [tautChartNorm] using h

theorem tautChartNorm_pos (z : Fin d → ℂ) : 0 < tautChartNorm z :=
  lt_of_lt_of_le zero_lt_one (one_le_tautChartNorm z)

theorem tautChartNorm_ne_zero (z : Fin d → ℂ) : tautChartNorm z ≠ 0 :=
  ne_of_gt (tautChartNorm_pos z)

/-- The normalized lift `(1, z) / √(1 + ‖z‖²)` of a chart coordinate. -/
def tautChartVec (z : Fin d → ℂ) : Fin (d + 1) → ℂ :=
  fun a => ((Real.sqrt (tautChartNorm z))⁻¹ : ℝ) * (Fin.cons 1 z : Fin (d + 1) → ℂ) a

theorem tautChartVec_apply (z : Fin d → ℂ) (a : Fin (d + 1)) :
    tautChartVec z a
      = ((Real.sqrt (tautChartNorm z))⁻¹ : ℝ) * (Fin.cons 1 z : Fin (d + 1) → ℂ) a :=
  rfl

theorem inv_sqrt_tautChartNorm_sq (z : Fin d → ℂ) :
    ((Real.sqrt (tautChartNorm z))⁻¹) ^ 2 = (tautChartNorm z)⁻¹ := by
  rw [inv_pow, Real.sq_sqrt (tautChartNorm_pos z).le]

theorem norm_sq_tautChartVec (z : Fin d → ℂ) (a : Fin (d + 1)) :
    ‖tautChartVec z a‖ ^ 2
      = (tautChartNorm z)⁻¹ * ‖(Fin.cons 1 z : Fin (d + 1) → ℂ) a‖ ^ 2 := by
  have hr : (0 : ℝ) ≤ (Real.sqrt (tautChartNorm z))⁻¹ := by positivity
  rw [tautChartVec_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
    mul_pow, inv_sqrt_tautChartNorm_sq]

theorem tautChartVec_mem_unitVectors (z : Fin d → ℂ) :
    tautChartVec z ∈ unitVectors (Fin (d + 1)) := by
  show (∑ a, ‖tautChartVec z a‖ ^ 2) = 1
  rw [Finset.sum_congr rfl (fun a _ => norm_sq_tautChartVec z a), ← Finset.mul_sum]
  have hsum : (∑ a, ‖(Fin.cons 1 z : Fin (d + 1) → ℂ) a‖ ^ 2) = tautChartNorm z := by
    rw [Fin.sum_univ_succ]
    simp [tautChartNorm]
  rw [hsum, inv_mul_cancel₀ (tautChartNorm_ne_zero z)]

/-- The standard affine chart of `ℂP^d` around the base point, in the projection model:
`z ↦ ` the rank-one projection onto the line spanned by `(1, z)`. -/
def tautChart (z : Fin d → ℂ) : CP d :=
  ⟨rankOneProj (tautChartVec z), rankOneProj_mem_cpSet (tautChartVec_mem_unitVectors z)⟩

@[simp]
theorem tautChart_entry (z : Fin d → ℂ) (a b : Fin (d + 1)) :
    entry (tautChart z) a b = tautChartVec z a * star (tautChartVec z b) := rfl

theorem tautChart_zero (d : ℕ) : tautChart (0 : Fin d → ℂ) = basePoint d := by
  refine (dualTautSection_eq_zero_iff _).mp (fun i j => ?_)
  rw [dualTautSection_apply, tautChart_entry]
  simp [tautChartVec_apply]

/-- **The section in the chart.**  Along the affine chart around its zero, the section
is `z ↦ (1 + ‖z‖²)⁻¹ z`: a *positive real* multiple of the identity of `ℂ^d`.  (Only the
`0`-th coordinate of each block is recorded; that is the coordinate in which the
trivialization of `L*` over the chart is written.) -/
def sectionChart (z : Fin d → ℂ) : Fin d → ℂ := fun i => dualTautSection (tautChart z) i 0

theorem sectionChart_apply (z : Fin d → ℂ) (i : Fin d) :
    sectionChart z i = ((tautChartNorm z)⁻¹ : ℝ) * z i := by
  have hs : star ((((Real.sqrt (tautChartNorm z))⁻¹ : ℝ) : ℂ) * 1)
      = (((Real.sqrt (tautChartNorm z))⁻¹ : ℝ) : ℂ) := by simp
  have hc : (((Real.sqrt (tautChartNorm z))⁻¹ : ℝ) : ℂ)
      * (((Real.sqrt (tautChartNorm z))⁻¹ : ℝ) : ℂ) = (((tautChartNorm z)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← pow_two, inv_sqrt_tautChartNorm_sq]
  have hre : ∀ A B : ℂ, A * z i * B = A * B * z i := by
    intro A B
    ring
  show tautChartVec z i.succ * star (tautChartVec z 0) = _
  rw [tautChartVec_apply, tautChartVec_apply, Fin.cons_succ, Fin.cons_zero, hs, hre, hc]

theorem sectionChart_eq_zero_iff (z : Fin d → ℂ) :
    (∀ i, sectionChart z i = 0) ↔ z = 0 := by
  constructor
  · intro h
    funext i
    have hi := h i
    rw [sectionChart_apply] at hi
    have hne : (((tautChartNorm z)⁻¹ : ℝ) : ℂ) ≠ 0 := by
      simpa using inv_ne_zero (tautChartNorm_ne_zero z)
    simpa using (mul_eq_zero.mp hi).resolve_left hne
  · intro h i
    rw [sectionChart_apply, h]
    simp

/-! ## 5. Transversality, in the form a mod-2 index consumes -/

/-- The straight-line homotopy in `ℂ^d` from the identity (`s = 0`) to the chart form of
the section (`s = 1`). -/
def tautChartHomotopy (s : ℝ) (z : Fin d → ℂ) : Fin d → ℂ :=
  fun i => (((1 - s) + s * (tautChartNorm z)⁻¹ : ℝ) : ℂ) * z i

theorem tautChartHomotopy_zero (z : Fin d → ℂ) : tautChartHomotopy 0 z = z := by
  funext i
  simp [tautChartHomotopy]

theorem tautChartHomotopy_one (z : Fin d → ℂ) : tautChartHomotopy 1 z = sectionChart z := by
  funext i
  rw [sectionChart_apply]
  simp [tautChartHomotopy]

/-- The homotopy coefficient is strictly positive at every time of the interval. -/
theorem tautChartHomotopy_coeff_pos {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (z : Fin d → ℂ) :
    0 < (1 - s) + s * (tautChartNorm z)⁻¹ := by
  have hinv : 0 < (tautChartNorm z)⁻¹ := inv_pos.mpr (tautChartNorm_pos z)
  rcases eq_or_lt_of_le hs0 with h | h
  · rw [← h]
    norm_num
  · have h1 : 0 ≤ 1 - s := by linarith
    have h2 : 0 < s * (tautChartNorm z)⁻¹ := mul_pos h hinv
    linarith

/-- **Transversality of the zero, mod-2 form.**  At every time `s ∈ [0, 1]` the homotopy
from the identity of `ℂ^d` to the chart form of the section has the origin as its only
zero.  So the section's zero is isolated and its local index equals that of the identity;
in particular it is odd.

No derivative, no determinant, no orientation of `ℂ^d` or of `ℂP^d` enters — which is the
whole point of running the campaign's obstruction mod `2`. -/
theorem tautChartHomotopy_eq_zero_iff {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (z : Fin d → ℂ) :
    (∀ i, tautChartHomotopy s z i = 0) ↔ z = 0 := by
  have hpos := tautChartHomotopy_coeff_pos hs0 hs1 z
  have hne : ((((1 - s) + s * (tautChartNorm z)⁻¹ : ℝ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
  constructor
  · intro h
    funext i
    have hi := h i
    simp only [tautChartHomotopy] at hi
    exact (mul_eq_zero.mp hi).resolve_left hne
  · intro h i
    simp only [tautChartHomotopy, h]
    simp

/-! ## 6. The column section: the one fixed by the projection itself

`dualTautSection` above is the `i`-th **row** of the rank-one projection `q`, and
`dualTautComponent_isSection` shows it is fixed by the *conjugate* projection `q̄`.  That is
the right normalisation for the dual line `L*`, but a downstream lane building
`H = ⊕ⱼ Lⱼ^{⊕dⱼ}` out of the projections `q` themselves needs a section fixed by `q`, i.e.
one satisfying `q *ᵥ σ = σ`.  That is the `i`-th **column**.

The two differ by an entrywise complex conjugation (`entry_symm`), so they have the same
zero locus; in the affine chart the column model is `z ↦ (1 + ‖z‖²)⁻¹ conj z` where the row
model is `z ↦ (1 + ‖z‖²)⁻¹ z`, and the two derivatives at the origin differ by complex
conjugation, a real-linear isomorphism of real determinant `(-1)^d`.  Mod `2` — which is
all the campaign's parity contradiction uses — they agree, exactly as this file's header
already records for `L` against `L*`. -/

/-- The section of the tautological line `L` over `CP d` attached to the `i`-th coordinate:
at the rank-one projection `q` it is the `i`-th **column** of `q`. -/
def tautColComponent (i : Fin (d + 1)) (x : CP d) : Fin (d + 1) → ℂ :=
  fun j => entry x j i

@[simp]
theorem tautColComponent_apply (i : Fin (d + 1)) (x : CP d) (j : Fin (d + 1)) :
    tautColComponent i x j = entry x j i := rfl

/-- **The column is a section of `L` itself**: `q *ᵥ (q eᵢ) = q eᵢ`, because the sum is the
`(j, i)` entry of `q * q = q`.  This is the identity `dualTautComponent_isSection` fails to
provide for the row, and the one a bundle built from `q` (rather than from `q̄`) needs. -/
theorem tautColComponent_isSection (i : Fin (d + 1)) (x : CP d) (j : Fin (d + 1)) :
    (∑ k, entry x j k * tautColComponent i x k) = tautColComponent i x j :=
  entry_sum_mul x j i

/-- The section of `L^{⊕d}` over `CP d` given by the `d` coordinates `1, …, d`. -/
def tautColSection (x : CP d) : Fin d → Fin (d + 1) → ℂ :=
  fun i => tautColComponent i.succ x

@[simp]
theorem tautColSection_apply (x : CP d) (i : Fin d) (j : Fin (d + 1)) :
    tautColSection x i j = entry x j i.succ := rfl

/-- The column section is the entrywise conjugate of the row section. -/
theorem tautColSection_eq_star (x : CP d) (i : Fin d) (j : Fin (d + 1)) :
    tautColSection x i j = star (dualTautSection x i j) := by
  rw [tautColSection_apply, dualTautSection_apply, entry_symm x j i.succ]

/-- **Exactly one zero, for the column section.**  Same zero locus as the row section, by
`entry_symm`. -/
theorem tautColSection_eq_zero_iff (x : CP d) :
    (∀ i j, tautColSection x i j = 0) ↔ x = basePoint d := by
  rw [← dualTautSection_eq_zero_iff]
  constructor
  · intro h i j
    have hi : star (dualTautSection x i j) = 0 := by
      rw [← tautColSection_eq_star]
      exact h i j
    simpa using congrArg star hi
  · intro h i j
    rw [tautColSection_eq_star, h i j, star_zero]

theorem continuous_tautColSection (d : ℕ) :
    Continuous fun x : CP d => tautColSection x := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simpa using continuous_entry j i.succ

end CPn

end GroupApproximation.AlgTop
