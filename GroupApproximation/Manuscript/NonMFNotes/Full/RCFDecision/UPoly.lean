import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Poly
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Univariate polynomials with multivariate coefficients

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof step "Fixed-dimensional
feasibility is decidable over the real closed field".  Eliminating a quantifier
`∃ x_i` views a polynomial as a polynomial in `x_i` whose coefficients are
polynomials in the remaining variables.  Such a polynomial is a list of
coefficients, lowest degree first (`List MvP`).  `toPoly ρ u` is the real
polynomial obtained by evaluating the coefficients at `ρ`.

Main facts:
* the symbolic ring operations and the derivative commute with `toPoly`;
* `coeffX i p` is `p` viewed as a polynomial in `x_i`, with
  `(toPoly ρ (coeffX i p)).eval r = mvEval (update ρ i r) p` (`eval_toPoly_coeffX`);
* for `bl` not vanishing at `ρ`, `toPoly ρ (b ++ [bl])` has degree `b.length` and
  leading coefficient `mvEval ρ bl`.
-/

namespace GroupApproximation.Full.NN11b

open Polynomial

noncomputable section

/-- The real polynomial with coefficients `mvEval ρ u_k`. -/
def toPoly (ρ : ℕ → ℝ) : List (List (ℤ × List ℕ)) → ℝ[X]
  | [] => 0
  | c :: u => C (mvEval ρ c) + X * toPoly ρ u

theorem toPoly_nil (ρ : ℕ → ℝ) : toPoly ρ [] = 0 := rfl

theorem toPoly_cons (ρ : ℕ → ℝ) (c : MvP) (u : List MvP) :
    toPoly ρ (c :: u) = C (mvEval ρ c) + X * toPoly ρ u := rfl

/-! ## Operations -/

/-- Sum of coefficient lists. -/
def upAdd : List MvP → List MvP → List MvP
  | [], v => v
  | a :: u, [] => a :: u
  | a :: u, b :: v => (a ++ b) :: upAdd u v

theorem toPoly_upAdd (ρ : ℕ → ℝ) : ∀ u v : List MvP,
    toPoly ρ (upAdd u v) = toPoly ρ u + toPoly ρ v
  | [], v => by
      show toPoly ρ v = toPoly ρ [] + toPoly ρ v
      rw [toPoly_nil, zero_add]
  | a :: u, [] => by
      show toPoly ρ (a :: u) = toPoly ρ (a :: u) + toPoly ρ []
      rw [toPoly_nil, add_zero]
  | a :: u, b :: v => by
      show C (mvEval ρ (a ++ b)) + X * toPoly ρ (upAdd u v)
        = (C (mvEval ρ a) + X * toPoly ρ u) + (C (mvEval ρ b) + X * toPoly ρ v)
      rw [toPoly_upAdd ρ u v, mvEval_append, C_add]
      ring

/-- Negation of a coefficient list. -/
def upNeg : List MvP → List MvP
  | [] => []
  | a :: u => mvNeg a :: upNeg u

theorem toPoly_upNeg (ρ : ℕ → ℝ) : ∀ u : List MvP, toPoly ρ (upNeg u) = -toPoly ρ u
  | [] => by
      show toPoly ρ [] = -toPoly ρ []
      rw [toPoly_nil, neg_zero]
  | a :: u => by
      show C (mvEval ρ (mvNeg a)) + X * toPoly ρ (upNeg u) = -(C (mvEval ρ a) + X * toPoly ρ u)
      rw [toPoly_upNeg ρ u, mvEval_neg, C_neg]
      ring

/-- Multiplication of a coefficient list by a scalar polynomial. -/
def upSmul (c : MvP) : List MvP → List MvP
  | [] => []
  | a :: u => mvMul c a :: upSmul c u

theorem toPoly_upSmul (ρ : ℕ → ℝ) (c : MvP) : ∀ u : List MvP,
    toPoly ρ (upSmul c u) = C (mvEval ρ c) * toPoly ρ u
  | [] => by
      show toPoly ρ [] = C (mvEval ρ c) * toPoly ρ []
      rw [toPoly_nil, mul_zero]
  | a :: u => by
      show C (mvEval ρ (mvMul c a)) + X * toPoly ρ (upSmul c u)
        = C (mvEval ρ c) * (C (mvEval ρ a) + X * toPoly ρ u)
      rw [toPoly_upSmul ρ c u, mvEval_mul, C_mul]
      ring

/-- Product of coefficient lists. -/
def upMul : List MvP → List MvP → List MvP
  | [], _ => []
  | a :: u, v => upAdd (upSmul a v) ([] :: upMul u v)

theorem toPoly_upMul (ρ : ℕ → ℝ) (v : List MvP) : ∀ u : List MvP,
    toPoly ρ (upMul u v) = toPoly ρ u * toPoly ρ v
  | [] => by
      show toPoly ρ [] = toPoly ρ [] * toPoly ρ v
      rw [toPoly_nil, zero_mul]
  | a :: u => by
      show toPoly ρ (upAdd (upSmul a v) ([] :: upMul u v))
        = (C (mvEval ρ a) + X * toPoly ρ u) * toPoly ρ v
      rw [toPoly_upAdd, toPoly_upSmul, toPoly_cons, toPoly_upMul ρ v u, mvEval_nil, C_0]
      ring

/-- Auxiliary derivative: `∑ (k + j) c_j X^j`. -/
def upDerivAux : ℕ → List MvP → List MvP
  | _, [] => []
  | k, c :: u => mvMul (mvConst (k : ℤ)) c :: upDerivAux (k + 1) u

theorem toPoly_upDerivAux (ρ : ℕ → ℝ) : ∀ (u : List MvP) (k : ℕ),
    toPoly ρ (upDerivAux k u) = C (k : ℝ) * toPoly ρ u + X * derivative (toPoly ρ u)
  | [], k => by
      show toPoly ρ [] = C (k : ℝ) * toPoly ρ [] + X * derivative (toPoly ρ [])
      rw [toPoly_nil, derivative_zero]
      ring
  | c :: u, k => by
      have h1 : C (((k + 1 : ℕ) : ℝ)) = C (k : ℝ) + 1 := by
        rw [Nat.cast_succ, C_add, C_1]
      have h2 : mvEval ρ (mvConst (k : ℤ)) = (k : ℝ) :=
        (mvEval_const ρ (k : ℤ)).trans (Int.cast_natCast k)
      show C (mvEval ρ (mvMul (mvConst (k : ℤ)) c)) + X * toPoly ρ (upDerivAux (k + 1) u)
        = C (k : ℝ) * (C (mvEval ρ c) + X * toPoly ρ u)
          + X * derivative (C (mvEval ρ c) + X * toPoly ρ u)
      rw [toPoly_upDerivAux ρ u (k + 1), mvEval_mul, h2, h1, derivative_add, derivative_C,
        derivative_mul, derivative_X, C_mul]
      ring

/-- The formal derivative of a coefficient list. -/
def upDeriv : List MvP → List MvP
  | [] => []
  | _ :: u => upDerivAux 1 u

theorem toPoly_upDeriv (ρ : ℕ → ℝ) : ∀ u : List MvP,
    toPoly ρ (upDeriv u) = derivative (toPoly ρ u)
  | [] => by
      show toPoly ρ [] = derivative (toPoly ρ [])
      rw [toPoly_nil, derivative_zero]
  | c :: u => by
      show toPoly ρ (upDerivAux 1 u) = derivative (C (mvEval ρ c) + X * toPoly ρ u)
      rw [toPoly_upDerivAux, derivative_add, derivative_C, derivative_mul, derivative_X,
        Nat.cast_one, C_1]
      ring

/-! ## Appending a top coefficient -/

theorem toPoly_append_single (ρ : ℕ → ℝ) (c : MvP) : ∀ u : List MvP,
    toPoly ρ (u ++ [c]) = toPoly ρ u + C (mvEval ρ c) * X ^ u.length
  | [] => by
      show C (mvEval ρ c) + X * toPoly ρ [] = toPoly ρ [] + C (mvEval ρ c) * X ^ 0
      rw [toPoly_nil, pow_zero]
      ring
  | a :: u => by
      show C (mvEval ρ a) + X * toPoly ρ (u ++ [c])
        = (C (mvEval ρ a) + X * toPoly ρ u) + C (mvEval ρ c) * X ^ (u.length + 1)
      rw [toPoly_append_single ρ c u]
      ring

theorem toPoly_replicate_nil (ρ : ℕ → ℝ) : ∀ k : ℕ, toPoly ρ (List.replicate k []) = 0
  | 0 => rfl
  | k + 1 => by
      show C (mvEval ρ []) + X * toPoly ρ (List.replicate k []) = 0
      rw [toPoly_replicate_nil ρ k, mvEval_nil, C_0]
      ring

theorem toPoly_monomial (ρ : ℕ → ℝ) (k : ℕ) (c : MvP) :
    toPoly ρ (List.replicate k [] ++ [c]) = C (mvEval ρ c) * X ^ k := by
  rw [toPoly_append_single, toPoly_replicate_nil, List.length_replicate, zero_add]

/-! ## Viewing a polynomial as a polynomial in one variable -/

/-- The monomial `c·x^e` as a polynomial in `x_i`. -/
def monoUP (i : ℕ) (c : ℤ) (e : List ℕ) : List MvP :=
  List.replicate (e.getD i 0) [] ++ [[(c, e.set i 0)]]

/-- `p` as a polynomial in `x_i`. -/
def coeffX (i : ℕ) : List (ℤ × List ℕ) → List MvP
  | [] => []
  | m :: p => upAdd (monoUP i m.1 m.2) (coeffX i p)

theorem eval_toPoly_coeffX (ρ : ℕ → ℝ) (i : ℕ) (r : ℝ) : ∀ p : MvP,
    (toPoly ρ (coeffX i p)).eval r = mvEval (Function.update ρ i r) p
  | [] => by
      show (toPoly ρ []).eval r = mvEval (Function.update ρ i r) []
      rw [toPoly_nil, eval_zero, mvEval_nil]
  | m :: p => by
      have hm : mvEval ρ [(m.1, m.2.set i 0)] = (m.1 : ℝ) * monoEval ρ (m.2.set i 0) := by
        show (m.1 : ℝ) * monoEval ρ (m.2.set i 0) + mvEval ρ [] = _
        rw [mvEval_nil, add_zero]
      show (toPoly ρ (upAdd (monoUP i m.1 m.2) (coeffX i p))).eval r
        = (m.1 : ℝ) * monoEval (Function.update ρ i r) m.2 + mvEval (Function.update ρ i r) p
      rw [toPoly_upAdd, eval_add, eval_toPoly_coeffX ρ i r p, monoUP, toPoly_monomial, hm,
        eval_mul, eval_C, eval_X_pow, monoEval_update]
      ring

/-! ## Coefficients, degree and leading coefficient -/

theorem getD_of_length_le {α : Type*} (d : α) : ∀ (u : List α) (N : ℕ), u.length ≤ N →
    u.getD N d = d
  | [], _, _ => List.getD_nil
  | _ :: _, 0, h => absurd h (by rw [List.length_cons]; omega)
  | _ :: u, N + 1, h => by
      rw [List.getD_cons_succ]
      exact getD_of_length_le d u N (by rw [List.length_cons] at h; omega)

theorem getD_append_single_length {α : Type*} (d c : α) : ∀ u : List α,
    (u ++ [c]).getD u.length d = c
  | [] => by
      show [c].getD 0 d = c
      exact List.getD_cons_zero
  | a :: u => by
      show (a :: (u ++ [c])).getD (u.length + 1) d = c
      rw [List.getD_cons_succ]
      exact getD_append_single_length d c u

theorem coeff_toPoly (ρ : ℕ → ℝ) : ∀ (u : List MvP) (k : ℕ),
    (toPoly ρ u).coeff k = mvEval ρ (u.getD k [])
  | [], k => by
      rw [toPoly_nil, coeff_zero, List.getD_nil, mvEval_nil]
  | c :: u, 0 => by
      rw [toPoly_cons, coeff_add, coeff_C_zero, coeff_X_mul_zero, add_zero, List.getD_cons_zero]
  | c :: u, k + 1 => by
      rw [toPoly_cons, coeff_add, coeff_C, if_neg (by omega : ¬(k + 1 = 0)), coeff_X_mul, zero_add,
        List.getD_cons_succ]
      exact coeff_toPoly ρ u k

theorem natDegree_toPoly_append (ρ : ℕ → ℝ) (b : List MvP) (bl : MvP)
    (hbl : mvEval ρ bl ≠ 0) : (toPoly ρ (b ++ [bl])).natDegree = b.length := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_toPoly, getD_of_length_le [] (b ++ [bl]) N
      (by rw [List.length_append, List.length_cons, List.length_nil]; omega), mvEval_nil]
  · rw [coeff_toPoly, getD_append_single_length]
    exact hbl

theorem leadingCoeff_toPoly_append (ρ : ℕ → ℝ) (b : List MvP) (bl : MvP)
    (hbl : mvEval ρ bl ≠ 0) : (toPoly ρ (b ++ [bl])).leadingCoeff = mvEval ρ bl := by
  rw [leadingCoeff, natDegree_toPoly_append ρ b bl hbl, coeff_toPoly,
    getD_append_single_length]

theorem toPoly_append_single_ne_zero (ρ : ℕ → ℝ) (b : List MvP) (bl : MvP)
    (hbl : mvEval ρ bl ≠ 0) : toPoly ρ (b ++ [bl]) ≠ 0 := by
  intro h
  apply hbl
  rw [← leadingCoeff_toPoly_append ρ b bl hbl, h, leadingCoeff_zero]

end

end GroupApproximation.Full.NN11b
