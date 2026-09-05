import Mathlib
import GroupApproximation.Analysis.LIXObstructionTautSection

/-!
# The affine chart at the zero, and nondegeneracy

Lane `lix-obstruction`, campaign target 3 (STW Problem LIX).

`LIXObstructionTautSection.lean` shows that the `d`-tuple of sections of the
tautological line `L → ℂP^d` cut out by the first `d` standard basis vectors has
exactly one zero, the line `e_d e_dᴴ`.  This file reads that section in the affine
chart at the zero and shows the zero is **nondegenerate**, which is what turns "one
zero" into "mod-2 Euler number one".

The chart is the usual one: `w ∈ ℂ^d` gives the line spanned by
`snoc w 1 = (w₁, …, w_d, 1)`, and `w = 0` is the zero of the section.  In the frame
`snoc w 1` of the tautological line, the section reads

```text
w ↦ (1 + ‖w‖²)⁻¹ · (w̄₁, …, w̄_d),
```

a positive scalar times componentwise conjugation.  Conjugation is an `ℝ`-linear
isomorphism of `ℂ^d`, so the zero is transverse.  (Its local index is `+1`, since
conjugating each of `d` coordinates is `d` reflections in each of `d` complex lines,
i.e. determinant `(-1)^d · (-1)^d = 1`; but no sign is needed for the mod-2 count,
only invertibility.)

## Main results

* `chartPoint` — the affine chart `ℂ^d → ℂP^d` at `e_d e_dᴴ`, and `chartPoint d 0`
  is the basepoint.
* `constSection_chartPoint` — the exact formula for the section in the chart.
* `chartPoint_eq_basepoint_iff` — the chart meets the zero only at `w = 0`.
* `conjPiEquiv` — componentwise conjugation as an `ℝ`-linear equivalence.
-/

namespace GroupApproximation
namespace STW59

open Matrix

/-! ### The affine chart -/

/-- The unit vector spanning the line of the chart at parameter `w`. -/
noncomputable def chartUnit (d : ℕ) (w : Fin d → ℂ) : Fin (d + 1) → ℂ :=
  fun i => (((Real.sqrt (1 + ∑ k, ‖w k‖ ^ 2))⁻¹ : ℝ) : ℂ) * Fin.snoc w 1 i

theorem snoc_sq_sum (d : ℕ) (w : Fin d → ℂ) :
    ∑ i, ‖(Fin.snoc w (1 : ℂ)) i‖ ^ 2 = (∑ k, ‖w k‖ ^ 2) + 1 := by
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

theorem chartUnit_mem_unitVectors (d : ℕ) (w : Fin d → ℂ) :
    chartUnit d w ∈ unitVectors (d + 1) := by
  have hS : (0 : ℝ) ≤ ∑ k, ‖w k‖ ^ 2 := Finset.sum_nonneg fun k _ => by positivity
  have hpos : (0 : ℝ) < 1 + ∑ k, ‖w k‖ ^ 2 := by linarith
  have hsq : Real.sqrt (1 + ∑ k, ‖w k‖ ^ 2) ^ 2 = 1 + ∑ k, ‖w k‖ ^ 2 :=
    Real.sq_sqrt hpos.le
  have hterm : ∀ i : Fin (d + 1), ‖chartUnit d w i‖ ^ 2
      = (1 + ∑ k, ‖w k‖ ^ 2)⁻¹ * ‖(Fin.snoc w (1 : ℂ)) i‖ ^ 2 := by
    intro i
    have hval : chartUnit d w i
        = (((Real.sqrt (1 + ∑ k, ‖w k‖ ^ 2))⁻¹ : ℝ) : ℂ) * Fin.snoc w 1 i := rfl
    rw [hval, norm_mul, Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs,
      inv_pow, hsq]
  rw [mem_unitVectors_iff]
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum, snoc_sq_sum]
  field_simp

/-- **The affine chart at the zero of the section.** -/
noncomputable def chartPoint (d : ℕ) (w : Fin d → ℂ) : CP d :=
  ⟨rankOne (chartUnit d w), rankOne_mem_cpSet (chartUnit_mem_unitVectors d w)⟩

theorem snoc_zero_one (d : ℕ) :
    Fin.snoc (0 : Fin d → ℂ) 1 = Pi.single (Fin.last d) (1 : ℂ) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast k =>
    have hne : (k.castSucc : Fin (d + 1)) ≠ Fin.last d := (Fin.castSucc_lt_last k).ne
    simp [Fin.snoc_castSucc, Pi.single_apply, hne]

theorem chartUnit_zero (d : ℕ) : chartUnit d 0 = Pi.single (Fin.last d) 1 := by
  have hval : chartUnit d (0 : Fin d → ℂ)
      = fun i => (((Real.sqrt (1 + ∑ k, ‖(0 : Fin d → ℂ) k‖ ^ 2))⁻¹ : ℝ) : ℂ)
          * Fin.snoc (0 : Fin d → ℂ) 1 i := rfl
  rw [hval, ← snoc_zero_one d]
  funext i
  simp

@[simp]
theorem chartPoint_zero (d : ℕ) : chartPoint d 0 = cpBasepoint d := by
  apply Subtype.ext
  show rankOne (chartUnit d 0) = rankOne (Pi.single (Fin.last d) 1)
  rw [chartUnit_zero]

/-! ### The section in the chart -/

/-- **The section, read in the frame `snoc w 1` of the chart.**

Up to the positive scalar `(1 + ‖w‖²)⁻¹` the `j`-th component is `w̄_j`.  So in this
chart the `d`-tuple of sections is componentwise conjugation, whose only zero is
`w = 0` and whose derivative there is the `ℝ`-linear isomorphism `conjPiEquiv`. -/
theorem constSection_chartPoint (d : ℕ) (w : Fin d → ℂ) (j : Fin d) (i : Fin (d + 1)) :
    constSection d (Pi.single j.castSucc 1) (chartPoint d w) i
      = (((1 + ∑ k, ‖w k‖ ^ 2 : ℝ)⁻¹ : ℝ) : ℂ) * (Fin.snoc w 1 i * star (w j)) := by
  have hS : (0 : ℝ) ≤ ∑ k, ‖w k‖ ^ 2 := Finset.sum_nonneg fun k _ => by positivity
  have hpos : (0 : ℝ) < 1 + ∑ k, ‖w k‖ ^ 2 := by linarith
  have hsq : Real.sqrt (1 + ∑ k, ‖w k‖ ^ 2) ^ 2 = 1 + ∑ k, ‖w k‖ ^ 2 :=
    Real.sq_sqrt hpos.le
  have hcoe : (((Real.sqrt (1 + ∑ k, ‖w k‖ ^ 2))⁻¹ : ℝ) : ℂ)
      * (((Real.sqrt (1 + ∑ k, ‖w k‖ ^ 2))⁻¹ : ℝ) : ℂ)
      = (((1 + ∑ k, ‖w k‖ ^ 2 : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← sq, ← inv_pow, hsq]
  rw [constSection_single_apply]
  show rankOne (chartUnit d w) i j.castSucc = _
  rw [rankOne_apply]
  have hi : chartUnit d w i
      = (((Real.sqrt (1 + ∑ k, ‖w k‖ ^ 2))⁻¹ : ℝ) : ℂ) * Fin.snoc w 1 i := rfl
  have hj : chartUnit d w j.castSucc
      = (((Real.sqrt (1 + ∑ k, ‖w k‖ ^ 2))⁻¹ : ℝ) : ℂ) * w j := by
    have h : chartUnit d w j.castSucc
        = (((Real.sqrt (1 + ∑ k, ‖w k‖ ^ 2))⁻¹ : ℝ) : ℂ) * Fin.snoc w 1 j.castSucc := rfl
    rw [h, Fin.snoc_castSucc]
  have hstar : star ((((Real.sqrt (1 + ∑ k, ‖w k‖ ^ 2))⁻¹ : ℝ) : ℂ))
      = (((Real.sqrt (1 + ∑ k, ‖w k‖ ^ 2))⁻¹ : ℝ) : ℂ) := Complex.conj_ofReal _
  rw [hi, hj, star_mul', hstar, ← hcoe]
  ring

/-- Inside the chart, the section vanishes only at `w = 0`. -/
theorem chartPoint_eq_basepoint_iff (d : ℕ) (w : Fin d → ℂ) :
    chartPoint d w = cpBasepoint d ↔ w = 0 := by
  constructor
  · intro h
    funext j
    have hsec : constSection d (Pi.single j.castSucc 1) (chartPoint d w) = 0 := by
      have hzero : ∀ k : Fin d,
          constSection d (Pi.single k.castSucc 1) (cpBasepoint d) = 0 :=
        (constSections_eq_zero_iff d (cpBasepoint d)).mpr rfl
      rw [h]; exact hzero j
    have hval := congrFun hsec (Fin.last d)
    rw [constSection_chartPoint] at hval
    simp only [Fin.snoc_last, one_mul, Pi.zero_apply] at hval
    have hS : (0 : ℝ) ≤ ∑ k, ‖w k‖ ^ 2 := Finset.sum_nonneg fun k _ => by positivity
    have hne : (((1 + ∑ k, ‖w k‖ ^ 2 : ℝ)⁻¹ : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
      linarith
    have := (mul_eq_zero.mp hval).resolve_left hne
    simpa using this
  · rintro rfl
    exact chartPoint_zero d

/-! ### The local model at the zero -/

/-- Componentwise complex conjugation on `ℂ^d`, as an `ℝ`-linear equivalence.  This is
the derivative at `w = 0` of the section read in the chart, so the unique zero of the
section is transverse. -/
noncomputable def conjPiEquiv (d : ℕ) : (Fin d → ℂ) ≃ₗ[ℝ] (Fin d → ℂ) :=
  LinearEquiv.piCongrRight fun _ => Complex.conjLIE.toLinearEquiv

@[simp]
theorem conjPiEquiv_apply (d : ℕ) (w : Fin d → ℂ) (j : Fin d) :
    conjPiEquiv d w j = star (w j) := rfl

end STW59
end GroupApproximation
