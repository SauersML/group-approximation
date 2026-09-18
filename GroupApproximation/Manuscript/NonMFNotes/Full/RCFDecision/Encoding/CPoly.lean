import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Poly
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fintype.BigOperators

/-!
# Complex polynomials as pairs of real polynomials

`non_mf_group_notes.tex`, `prop:mf-upper-bound`, printed sentence `9eae4d68673a`
("`Φ(P,n,c)` is a first-order sentence over the reals"), feeding
`thm:mf-arithmetic`.  A complex quantity built from the real and imaginary parts
of the variables is carried as a pair `(re, im)` of integer polynomials
(`cpEval`).  Sums, products, conjugates and constants are computed symbolically,
and `encNormSq` is the polynomial `∑_r |z_r|²`.
-/

namespace GroupApproximation.Full.NN11b

/-- A complex polynomial: its real and imaginary parts. -/
abbrev CP := MvP × MvP

/-- Evaluation of a complex polynomial. -/
def cpEval (ρ : ℕ → ℝ) (z : MvP × MvP) : ℂ := ⟨mvEval ρ z.1, mvEval ρ z.2⟩

theorem cpEval_re (ρ : ℕ → ℝ) (z : MvP × MvP) : (cpEval ρ z).re = mvEval ρ z.1 := rfl

theorem cpEval_im (ρ : ℕ → ℝ) (z : MvP × MvP) : (cpEval ρ z).im = mvEval ρ z.2 := rfl

theorem cpEval_eq_zero_iff (ρ : ℕ → ℝ) (z : MvP × MvP) :
    (mvEval ρ z.1 = 0 ∧ mvEval ρ z.2 = 0) ↔ cpEval ρ z = 0 :=
  ⟨fun h => Complex.ext (h.1.trans Complex.zero_re.symm) (h.2.trans Complex.zero_im.symm),
    fun h => ⟨(congrArg Complex.re h).trans Complex.zero_re,
      (congrArg Complex.im h).trans Complex.zero_im⟩⟩

/-- The zero complex polynomial. -/
def cpZero : MvP × MvP := ([], [])

theorem cpEval_zero (ρ : ℕ → ℝ) : cpEval ρ cpZero = 0 :=
  Complex.ext ((mvEval_nil ρ).trans Complex.zero_re.symm)
    ((mvEval_nil ρ).trans Complex.zero_im.symm)

/-- The integer constant `c`. -/
def cpOfInt (c : ℤ) : MvP × MvP := (mvConst c, [])

theorem cpEval_ofInt (ρ : ℕ → ℝ) (c : ℤ) : cpEval ρ (cpOfInt c) = (c : ℂ) :=
  Complex.ext ((mvEval_const ρ c).trans (Complex.intCast_re c).symm)
    ((mvEval_nil ρ).trans (Complex.intCast_im c).symm)

/-- Sum of complex polynomials. -/
def cpAdd (z w : MvP × MvP) : MvP × MvP := (z.1 ++ w.1, z.2 ++ w.2)

theorem cpEval_add (ρ : ℕ → ℝ) (z w : MvP × MvP) :
    cpEval ρ (cpAdd z w) = cpEval ρ z + cpEval ρ w := by
  apply Complex.ext
  · rw [Complex.add_re, cpEval_re, cpEval_re, cpEval_re]
    exact mvEval_append ρ w.1 z.1
  · rw [Complex.add_im, cpEval_im, cpEval_im, cpEval_im]
    exact mvEval_append ρ w.2 z.2

/-- Negation of a complex polynomial. -/
def cpNeg (z : MvP × MvP) : MvP × MvP := (mvNeg z.1, mvNeg z.2)

theorem cpEval_neg (ρ : ℕ → ℝ) (z : MvP × MvP) : cpEval ρ (cpNeg z) = -cpEval ρ z := by
  apply Complex.ext
  · rw [Complex.neg_re, cpEval_re, cpEval_re]
    exact mvEval_neg ρ z.1
  · rw [Complex.neg_im, cpEval_im, cpEval_im]
    exact mvEval_neg ρ z.2

/-- Product of complex polynomials. -/
def cpMul (z w : MvP × MvP) : MvP × MvP :=
  (mvMul z.1 w.1 ++ mvNeg (mvMul z.2 w.2), mvMul z.1 w.2 ++ mvMul z.2 w.1)

theorem cpEval_mul (ρ : ℕ → ℝ) (z w : MvP × MvP) :
    cpEval ρ (cpMul z w) = cpEval ρ z * cpEval ρ w := by
  apply Complex.ext
  · rw [Complex.mul_re, cpEval_re, cpEval_re, cpEval_re, cpEval_im, cpEval_im]
    show mvEval ρ (mvMul z.1 w.1 ++ mvNeg (mvMul z.2 w.2))
      = mvEval ρ z.1 * mvEval ρ w.1 - mvEval ρ z.2 * mvEval ρ w.2
    rw [mvEval_append, mvEval_neg, mvEval_mul, mvEval_mul, sub_eq_add_neg]
  · rw [Complex.mul_im, cpEval_im, cpEval_re, cpEval_re, cpEval_im, cpEval_im]
    show mvEval ρ (mvMul z.1 w.2 ++ mvMul z.2 w.1)
      = mvEval ρ z.1 * mvEval ρ w.2 + mvEval ρ z.2 * mvEval ρ w.1
    rw [mvEval_append, mvEval_mul, mvEval_mul]

/-- Complex conjugate of a complex polynomial. -/
def cpConj (z : MvP × MvP) : MvP × MvP := (z.1, mvNeg z.2)

theorem cpEval_conj (ρ : ℕ → ℝ) (z : MvP × MvP) :
    cpEval ρ (cpConj z) = star (cpEval ρ z) := by
  apply Complex.ext
  · exact (Complex.conj_re (cpEval ρ z)).symm
  · exact (mvEval_neg ρ z.2).trans (Complex.conj_im (cpEval ρ z)).symm

/-! ## Sums over a range -/

theorem mvEval_flatMap_range (ρ : ℕ → ℝ) (g : ℕ → MvP) :
    ∀ d : ℕ, mvEval ρ ((List.range d).flatMap g) = ∑ s ∈ Finset.range d, mvEval ρ (g s)
  | 0 => by
      show mvEval ρ [] = ∑ s ∈ Finset.range 0, mvEval ρ (g s)
      rw [Finset.sum_range_zero, mvEval_nil]
  | d + 1 => by
      have hr : List.range (d + 1) = List.range d ++ [d] := List.range_succ
      rw [hr, List.flatMap_append, mvEval_append, mvEval_flatMap_range ρ g d,
        Finset.sum_range_succ, List.flatMap_singleton]

theorem mvEval_flatMap_range_fin (ρ : ℕ → ℝ) (g : ℕ → MvP) (d : ℕ) :
    mvEval ρ ((List.range d).flatMap g) = ∑ s : Fin d, mvEval ρ (g s) :=
  (mvEval_flatMap_range ρ g d).trans (Fin.sum_univ_eq_sum_range (fun s => mvEval ρ (g s)) d).symm

/-- The complex polynomial `∑_{s < d} f s`. -/
def cpSumRange (d : ℕ) (f : ℕ → MvP × MvP) : MvP × MvP :=
  ((List.range d).flatMap fun s => (f s).1, (List.range d).flatMap fun s => (f s).2)

theorem cpEval_sumRange (ρ : ℕ → ℝ) (d : ℕ) (f : ℕ → MvP × MvP) :
    cpEval ρ (cpSumRange d f) = ∑ s : Fin d, cpEval ρ (f s) := by
  apply Complex.ext
  · rw [Complex.re_sum]
    exact mvEval_flatMap_range_fin ρ (fun s => (f s).1) d
  · rw [Complex.im_sum]
    exact mvEval_flatMap_range_fin ρ (fun s => (f s).2) d

/-- The polynomial `∑_{r < d} |f r|²`. -/
def encNormSq (d : ℕ) (f : ℕ → MvP × MvP) : MvP :=
  (List.range d).flatMap fun r => mvMul (f r).1 (f r).1 ++ mvMul (f r).2 (f r).2

theorem mvEval_encNormSq (ρ : ℕ → ℝ) (d : ℕ) (f : ℕ → MvP × MvP) :
    mvEval ρ (encNormSq d f) = ∑ r : Fin d, Complex.normSq (cpEval ρ (f r)) := by
  rw [encNormSq, mvEval_flatMap_range_fin]
  refine Finset.sum_congr rfl fun r _ => ?_
  show mvEval ρ (mvMul (f r).1 (f r).1 ++ mvMul (f r).2 (f r).2)
    = Complex.normSq (cpEval ρ (f r))
  rw [Complex.normSq_apply, cpEval_re, cpEval_im, mvEval_append, mvEval_mul, mvEval_mul]

end GroupApproximation.Full.NN11b
