import Mathlib.Data.Real.Basic

/-!
# Multivariate integer polynomials as monomial lists

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof step "Fixed-dimensional
feasibility is decidable over the real closed field": the decision procedure
manipulates polynomials with integer coefficients symbolically.  A polynomial
is a list of monomials `(c, e)`, with `e = [k₀, k₁, …]` standing for
`c · x₀^{k₀} x₁^{k₁} ⋯`.  No normal form is imposed: only evaluation matters.

The main computation here is `monoEval_update`, which splits off the power of one variable.
The coefficient extraction built on it lives in `UPoly`.
-/

namespace GroupApproximation.Full.NN11b

/-- Evaluation of an exponent vector at a real assignment. -/
def monoEval : (ℕ → ℝ) → List ℕ → ℝ
  | _, [] => 1
  | ρ, k :: e => ρ 0 ^ k * monoEval (fun j => ρ (j + 1)) e

theorem monoEval_nil (ρ : ℕ → ℝ) : monoEval ρ [] = 1 := rfl

theorem monoEval_cons (ρ : ℕ → ℝ) (k : ℕ) (e : List ℕ) :
    monoEval ρ (k :: e) = ρ 0 ^ k * monoEval (fun j => ρ (j + 1)) e := rfl

/-- Multivariate integer polynomials: lists of monomials. -/
abbrev MvP := List (ℤ × List ℕ)

/-- Evaluation of a polynomial at a real assignment. -/
def mvEval (ρ : ℕ → ℝ) : List (ℤ × List ℕ) → ℝ
  | [] => 0
  | m :: p => (m.1 : ℝ) * monoEval ρ m.2 + mvEval ρ p

theorem mvEval_nil (ρ : ℕ → ℝ) : mvEval ρ [] = 0 := rfl

theorem mvEval_cons (ρ : ℕ → ℝ) (m : ℤ × List ℕ) (p : MvP) :
    mvEval ρ (m :: p) = (m.1 : ℝ) * monoEval ρ m.2 + mvEval ρ p := rfl

theorem mvEval_append (ρ : ℕ → ℝ) (q : MvP) : ∀ p : MvP,
    mvEval ρ (p ++ q) = mvEval ρ p + mvEval ρ q
  | [] => by
      show mvEval ρ q = mvEval ρ [] + mvEval ρ q
      rw [mvEval_nil, zero_add]
  | m :: p => by
      show (m.1 : ℝ) * monoEval ρ m.2 + mvEval ρ (p ++ q)
        = ((m.1 : ℝ) * monoEval ρ m.2 + mvEval ρ p) + mvEval ρ q
      rw [mvEval_append ρ q p]
      ring

/-! ## Exponent arithmetic -/

/-- Pointwise sum of exponent vectors. -/
def addExp : List ℕ → List ℕ → List ℕ
  | [], f => f
  | a :: e, [] => a :: e
  | a :: e, b :: f => (a + b) :: addExp e f

theorem addExp_nil_left (f : List ℕ) : addExp [] f = f := rfl

theorem addExp_cons_nil (a : ℕ) (e : List ℕ) : addExp (a :: e) [] = a :: e := rfl

theorem addExp_cons_cons (a b : ℕ) (e f : List ℕ) :
    addExp (a :: e) (b :: f) = (a + b) :: addExp e f := rfl

theorem monoEval_addExp : ∀ (e f : List ℕ) (ρ : ℕ → ℝ),
    monoEval ρ (addExp e f) = monoEval ρ e * monoEval ρ f
  | [], f, ρ => by rw [addExp_nil_left, monoEval_nil, one_mul]
  | a :: e, [], ρ => by rw [addExp_cons_nil, monoEval_nil, mul_one]
  | a :: e, b :: f, ρ => by
      rw [addExp_cons_cons, monoEval_cons, monoEval_cons, monoEval_cons,
        monoEval_addExp e f, pow_add]
      ring

/-- The exponent vector of the variable `x_i`. -/
def varExp : ℕ → List ℕ
  | 0 => [1]
  | i + 1 => 0 :: varExp i

theorem monoEval_varExp : ∀ (i : ℕ) (ρ : ℕ → ℝ), monoEval ρ (varExp i) = ρ i
  | 0, ρ => by
      show ρ 0 ^ 1 * monoEval (fun j => ρ (j + 1)) [] = ρ 0
      rw [monoEval_nil, pow_one, mul_one]
  | i + 1, ρ => by
      show ρ 0 ^ 0 * monoEval (fun j => ρ (j + 1)) (varExp i) = ρ (i + 1)
      rw [monoEval_varExp i, pow_zero, one_mul]

/-! ## Ring operations -/

/-- Multiplication of a polynomial by one monomial `c·x^e`. -/
def mvMulMono (c : ℤ) (e : List ℕ) : List (ℤ × List ℕ) → List (ℤ × List ℕ)
  | [] => []
  | m :: p => (c * m.1, addExp e m.2) :: mvMulMono c e p

theorem mvEval_mulMono (ρ : ℕ → ℝ) (c : ℤ) (e : List ℕ) : ∀ p : MvP,
    mvEval ρ (mvMulMono c e p) = (c : ℝ) * monoEval ρ e * mvEval ρ p
  | [] => by
      show mvEval ρ [] = (c : ℝ) * monoEval ρ e * mvEval ρ []
      rw [mvEval_nil, mul_zero]
  | m :: p => by
      show ((c * m.1 : ℤ) : ℝ) * monoEval ρ (addExp e m.2) + mvEval ρ (mvMulMono c e p)
        = (c : ℝ) * monoEval ρ e * ((m.1 : ℝ) * monoEval ρ m.2 + mvEval ρ p)
      rw [mvEval_mulMono ρ c e p, monoEval_addExp, Int.cast_mul]
      ring

/-- Product of polynomials. -/
def mvMul : List (ℤ × List ℕ) → List (ℤ × List ℕ) → List (ℤ × List ℕ)
  | [], _ => []
  | m :: p, q => mvMulMono m.1 m.2 q ++ mvMul p q

theorem mvEval_mul (ρ : ℕ → ℝ) (q : MvP) : ∀ p : MvP,
    mvEval ρ (mvMul p q) = mvEval ρ p * mvEval ρ q
  | [] => by
      show mvEval ρ [] = mvEval ρ [] * mvEval ρ q
      rw [mvEval_nil, zero_mul]
  | m :: p => by
      show mvEval ρ (mvMulMono m.1 m.2 q ++ mvMul p q)
        = ((m.1 : ℝ) * monoEval ρ m.2 + mvEval ρ p) * mvEval ρ q
      rw [mvEval_append, mvEval_mulMono, mvEval_mul ρ q p]
      ring

/-- Negation of a polynomial. -/
def mvNeg : List (ℤ × List ℕ) → List (ℤ × List ℕ)
  | [] => []
  | m :: p => (-m.1, m.2) :: mvNeg p

theorem mvEval_neg (ρ : ℕ → ℝ) : ∀ p : MvP, mvEval ρ (mvNeg p) = -mvEval ρ p
  | [] => by
      show mvEval ρ [] = -mvEval ρ []
      rw [mvEval_nil, neg_zero]
  | m :: p => by
      show ((-m.1 : ℤ) : ℝ) * monoEval ρ m.2 + mvEval ρ (mvNeg p)
        = -((m.1 : ℝ) * monoEval ρ m.2 + mvEval ρ p)
      rw [mvEval_neg ρ p, Int.cast_neg]
      ring

/-- The constant polynomial `c`. -/
def mvConst (c : ℤ) : MvP := [(c, [])]

theorem mvEval_const (ρ : ℕ → ℝ) (c : ℤ) : mvEval ρ (mvConst c) = (c : ℝ) := by
  show (c : ℝ) * monoEval ρ [] + mvEval ρ [] = (c : ℝ)
  rw [monoEval_nil, mvEval_nil, mul_one, add_zero]

/-- The variable `x_i`. -/
def mvVar (i : ℕ) : MvP := [(1, varExp i)]

theorem mvEval_var (ρ : ℕ → ℝ) (i : ℕ) : mvEval ρ (mvVar i) = ρ i := by
  show ((1 : ℤ) : ℝ) * monoEval ρ (varExp i) + mvEval ρ [] = ρ i
  rw [monoEval_varExp, mvEval_nil, Int.cast_one, one_mul, add_zero]

/-! ## Splitting off one variable -/

theorem shift_update_zero (ρ : ℕ → ℝ) (r : ℝ) :
    (fun j => Function.update ρ 0 r (j + 1)) = fun j => ρ (j + 1) := by
  funext j
  exact Function.update_of_ne (Nat.succ_ne_zero j) r ρ

theorem shift_update_succ (ρ : ℕ → ℝ) (i : ℕ) (r : ℝ) :
    (fun j => Function.update ρ (i + 1) r (j + 1))
      = Function.update (fun j => ρ (j + 1)) i r := by
  funext j
  show Function.update ρ (i + 1) r (j + 1) = Function.update (fun j => ρ (j + 1)) i r j
  by_cases h : j = i
  · subst h
    rw [Function.update_self, Function.update_self]
  · have h' : j + 1 ≠ i + 1 := by omega
    rw [Function.update_of_ne h', Function.update_of_ne h]

/-- Splitting the power of `x_i` off a monomial. -/
theorem monoEval_update : ∀ (e : List ℕ) (i : ℕ) (ρ : ℕ → ℝ) (r : ℝ),
    monoEval (Function.update ρ i r) e = r ^ (e.getD i 0) * monoEval ρ (e.set i 0)
  | [], i, ρ, r => by
      rw [List.getD_nil, List.set_nil, monoEval_nil, monoEval_nil, pow_zero, mul_one]
  | k :: e, 0, ρ, r => by
      have hs := shift_update_zero ρ r
      calc monoEval (Function.update ρ 0 r) (k :: e)
          = Function.update ρ 0 r 0 ^ k
              * monoEval (fun j => Function.update ρ 0 r (j + 1)) e := rfl
        _ = r ^ k * monoEval (fun j => ρ (j + 1)) e := by
              rw [Function.update_self]
              exact congrArg (fun t => r ^ k * monoEval t e) hs
        _ = r ^ ((k :: e).getD 0 0) * monoEval ρ ((k :: e).set 0 0) := by
              rw [List.getD_cons_zero, List.set_cons_zero, monoEval_cons, pow_zero, one_mul]
  | k :: e, i + 1, ρ, r => by
      have hs := shift_update_succ ρ i r
      have h0 : Function.update ρ (i + 1) r 0 = ρ 0 :=
        Function.update_of_ne (by omega) r ρ
      calc monoEval (Function.update ρ (i + 1) r) (k :: e)
          = Function.update ρ (i + 1) r 0 ^ k
              * monoEval (fun j => Function.update ρ (i + 1) r (j + 1)) e := rfl
        _ = ρ 0 ^ k * monoEval (Function.update (fun j => ρ (j + 1)) i r) e := by
              rw [h0]
              exact congrArg (fun t => ρ 0 ^ k * monoEval t e) hs
        _ = ρ 0 ^ k * (r ^ (e.getD i 0) * monoEval (fun j => ρ (j + 1)) (e.set i 0)) := by
              rw [monoEval_update e i]
        _ = r ^ ((k :: e).getD (i + 1) 0) * monoEval ρ ((k :: e).set (i + 1) 0) := by
              rw [List.getD_cons_succ, List.set_cons_succ, monoEval_cons]
              ring

end GroupApproximation.Full.NN11b
