import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Elim
import GroupApproximation.Manuscript.MFRecognition.PrintedTarskiCertificateSyntax

/-!
# Prenex sentences as printed real formulas

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof step "Fixed-dimensional
feasibility is decidable over the real closed field".  This file translates a prenex
sentence `qs. f` (prefix `qs`, matrix `f` in disjunctive normal form over sign atoms of
integer polynomials) into the printed syntax `RealFormula` of
`MFRecognition/PrintedTarskiCertificateSyntax.lean`, preserving truth
(`holds_prenexFormula`).  Combined with `decidePrenex_iff`, `decidePrenex` then decides
truth of the translated sentences (`decidePrenex_iff_holds`).
-/

namespace GroupApproximation.Full.NN11b

open GroupApproximation.Manuscript.MFRecognition.Certificates

/-! ## Terms -/

/-- The term `t^k`. -/
def realPowTerm (t : RealTerm) : ℕ → RealTerm
  | 0 => RealTerm.const 1
  | k + 1 => RealTerm.mul t (realPowTerm t k)

theorem eval_realPowTerm (ρ : ℕ → ℝ) (t : RealTerm) :
    ∀ k : ℕ, (realPowTerm t k).eval ρ = t.eval ρ ^ k
  | 0 => by
      show ((1 : ℤ) : ℝ) = t.eval ρ ^ 0
      rw [Int.cast_one, pow_zero]
  | k + 1 => by
      show t.eval ρ * (realPowTerm t k).eval ρ = t.eval ρ ^ (k + 1)
      rw [eval_realPowTerm ρ t k, pow_succ']

/-- The monomial `∏_j x_{o+j}^{e_j}`. -/
def realMonoTerm : ℕ → List ℕ → RealTerm
  | _, [] => RealTerm.const 1
  | o, k :: e => RealTerm.mul (realPowTerm (RealTerm.var o) k) (realMonoTerm (o + 1) e)

theorem eval_realMonoTerm (ρ : ℕ → ℝ) :
    ∀ (o : ℕ) (e : List ℕ), (realMonoTerm o e).eval ρ = monoEval (fun j => ρ (j + o)) e
  | o, [] => by
      show ((1 : ℤ) : ℝ) = monoEval (fun j => ρ (j + o)) []
      rw [Int.cast_one, monoEval_nil]
  | o, k :: e => by
      show (realPowTerm (RealTerm.var o) k).eval ρ * (realMonoTerm (o + 1) e).eval ρ =
        ρ (0 + o) ^ k * monoEval (fun j => ρ (j + 1 + o)) e
      rw [eval_realPowTerm, RealTerm.eval_var, eval_realMonoTerm ρ (o + 1) e, Nat.zero_add]
      have h : (fun j => ρ (j + (o + 1))) = fun j => ρ (j + 1 + o) :=
        funext fun j => congrArg ρ (by omega)
      rw [h]

/-- The polynomial `∑ c · x^e` as a term. -/
def realMvTerm : MvP → RealTerm
  | [] => RealTerm.const 0
  | m :: p => RealTerm.add (RealTerm.mul (RealTerm.const m.1) (realMonoTerm 0 m.2)) (realMvTerm p)

theorem eval_realMvTerm (ρ : ℕ → ℝ) : ∀ p : MvP, (realMvTerm p).eval ρ = mvEval ρ p
  | [] => by
      show ((0 : ℤ) : ℝ) = mvEval ρ []
      rw [Int.cast_zero, mvEval_nil]
  | m :: p => by
      show (m.1 : ℝ) * (realMonoTerm 0 m.2).eval ρ + (realMvTerm p).eval ρ = mvEval ρ (m :: p)
      have h0 : (fun j => ρ (j + 0)) = ρ := funext fun j => congrArg ρ (Nat.add_zero j)
      rw [eval_realMonoTerm, h0, eval_realMvTerm ρ p, mvEval_cons]

/-! ## Formulas -/

/-- A sign atom: `(true, p)` is `0 < p`, written `¬ p ≤ 0`; `(false, p)` is `p = 0`. -/
def atomFormula : Atom → RealFormula
  | (true, p) => RealFormula.not (RealFormula.leZero (realMvTerm p))
  | (false, p) => RealFormula.eqZero (realMvTerm p)

theorem holds_atomFormula (ρ : ℕ → ℝ) : ∀ a : Atom, (atomFormula a).Holds ρ ↔ atomHolds ρ a
  | (true, p) => by
      show ¬ (realMvTerm p).eval ρ ≤ 0 ↔ 0 < mvEval ρ p
      rw [eval_realMvTerm, not_le]
  | (false, p) => by
      show (realMvTerm p).eval ρ = 0 ↔ mvEval ρ p = 0
      rw [eval_realMvTerm]

/-- A conjunction of atoms; the empty conjunction is `0 = 0`. -/
def guardFormula : List Atom → RealFormula
  | [] => RealFormula.eqZero (RealTerm.const 0)
  | a :: g => RealFormula.and (atomFormula a) (guardFormula g)

theorem holds_guardFormula (ρ : ℕ → ℝ) :
    ∀ g : List Atom, (guardFormula g).Holds ρ ↔ guardHolds ρ g
  | [] => by
      show ((0 : ℤ) : ℝ) = 0 ↔ guardHolds ρ []
      exact ⟨fun _ => guardHolds_nil ρ, fun _ => Int.cast_zero⟩
  | a :: g => by
      show (atomFormula a).Holds ρ ∧ (guardFormula g).Holds ρ ↔ guardHolds ρ (a :: g)
      rw [guardHolds_cons, holds_atomFormula, holds_guardFormula ρ g]

/-- A disjunction of conjunctions; the empty disjunction is `¬ 0 = 0`. -/
def qfFormula : List (List Atom) → RealFormula
  | [] => RealFormula.not (RealFormula.eqZero (RealTerm.const 0))
  | c :: f => RealFormula.or (guardFormula c) (qfFormula f)

theorem holds_qfFormula (ρ : ℕ → ℝ) :
    ∀ f : List (List Atom), (qfFormula f).Holds ρ ↔ qfHolds ρ f
  | [] => by
      show ¬ ((0 : ℤ) : ℝ) = 0 ↔ qfHolds ρ []
      exact ⟨fun h => (h Int.cast_zero).elim, fun h => (qfHolds_nil ρ h).elim⟩
  | c :: f => by
      show (guardFormula c).Holds ρ ∨ (qfFormula f).Holds ρ ↔ qfHolds ρ (c :: f)
      rw [qfHolds_cons, holds_guardFormula, holds_qfFormula ρ f]

/-- The prenex sentence `qs. f` as a printed real formula. -/
def prenexFormula : List (Bool × ℕ) → List (List Atom) → RealFormula
  | [], f => qfFormula f
  | (true, i) :: qs, f => RealFormula.ex i (prenexFormula qs f)
  | (false, i) :: qs, f => RealFormula.all i (prenexFormula qs f)

/-- **The translation preserves truth.** -/
theorem holds_prenexFormula : ∀ (qs : List (Bool × ℕ)) (f : List (List Atom)) (ρ : ℕ → ℝ),
    (prenexFormula qs f).Holds ρ ↔ PHolds qs f ρ
  | [], f, ρ => by
      show (qfFormula f).Holds ρ ↔ qfHolds ρ f
      exact holds_qfFormula ρ f
  | (true, i) :: qs, f, ρ => by
      show (∃ r : ℝ, (prenexFormula qs f).Holds (Function.update ρ i r)) ↔
        ∃ r : ℝ, PHolds qs f (Function.update ρ i r)
      exact exists_congr fun r => holds_prenexFormula qs f (Function.update ρ i r)
  | (false, i) :: qs, f, ρ => by
      show (∀ r : ℝ, (prenexFormula qs f).Holds (Function.update ρ i r)) ↔
        ∀ r : ℝ, PHolds qs f (Function.update ρ i r)
      exact forall_congr' fun r => holds_prenexFormula qs f (Function.update ρ i r)

/-- **`decidePrenex` decides the translated sentences** at the zero assignment. -/
theorem decidePrenex_iff_holds (φ : List (Bool × ℕ) × List (List Atom)) :
    decidePrenex φ = true ↔ (prenexFormula φ.1 φ.2).Holds fun _ => 0 := by
  rw [decidePrenex_iff, holds_prenexFormula]

end GroupApproximation.Full.NN11b
