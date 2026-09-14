import GroupApproximation.Manuscript.SimpleKazhdanSofic.SturmianComputability
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LanguageReducesToWordProblem
import GroupApproximation.Meta.AxiomGuard

/-!
# Solvable word problems and the Fibonacci subshift

`simple_kazhdan_sofic_group.tex` (origin tip 696c4b602), corollary `cor:wp`, first two sentences:

> The word problem of `G_X` has the Turing degree of the language `L(X)` of `X`. In particular `G_X`
> has solvable word problem if and only if `L(X)` is recursive, as for the Fibonacci subshift
> `X_{(3-√5)/2}` below.

The only open piece here is ms-traces-3's `PrintedWordProblemReducesToLanguage` ("`L(X)` computes
the word problem"), so the endpoints below take it as their one hypothesis. The other pieces are
proved:
* `printedWordProblemDegreeEqLanguage_of`: with the landed `printedLanguageReducesToWordProblem`,
  the word problem and `L(X)` are Turing equivalent;
* `printedSolvableWordProblemIffRecursiveLanguage_of`: Turing equivalent functions are computable
  together;
* `partrec_slopeOracle_fibonacci`: the cut of `α = (3 - √5)/2` is primitive recursive, since
  `a < bα` exactly when `2a < 3b` and `5b² < (3b - 2a)²`;
* `printedFibonacciSolvableWordProblem_of`: the word problem of `G_{X_α}` reduces to `L(X_α)`, which
  reduces to the cut of `α` (`printedSlopeComputesSturmianLanguage`), which is computable.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open SturmianComputability

/-- Turing equivalent functions are computable together. -/
theorem partrec_iff_of_turingEquivalent {f g : ℕ →. ℕ} (h : TuringEquivalent f g) :
    Partrec f ↔ Partrec g :=
  ⟨fun hf => partrec_iff_forall_turingReducible.2 fun _ => h.2.trans hf.turingReducible,
    fun hg => partrec_iff_forall_turingReducible.2 fun _ => h.1.trans hg.turingReducible⟩

/-- **`cor:wp`, first sentence**, from the one open piece `L(X)` computes the word problem. -/
theorem printedWordProblemDegreeEqLanguage_of (hc : PrintedWordProblemReducesToLanguage) :
    PrintedWordProblemDegreeEqLanguage :=
  fun A _ _ _ _ _ S _ _ => ⟨hc A S, printedLanguageReducesToWordProblem A S⟩

/-- **`cor:wp`, second sentence**, from the one open piece `L(X)` computes the word problem. -/
theorem printedSolvableWordProblemIffRecursiveLanguage_of
    (hc : PrintedWordProblemReducesToLanguage) : PrintedSolvableWordProblemIffRecursiveLanguage :=
  fun A _ _ _ _ _ S hinf hmin =>
    partrec_iff_of_turingEquivalent (printedWordProblemDegreeEqLanguage_of hc A S hinf hmin)

/-- The division-free cut of `(3 - √5)/2`: `a < bα` exactly when `2a < 3b` and
`5b² < (3b - 2a)²`. -/
theorem natCast_lt_mul_fibonacci_iff (a b : ℕ) :
    (a : ℝ) < (b : ℝ) * ((3 - Real.sqrt 5) / 2) ↔
      2 * a < 3 * b ∧ 5 * (b * b) < (3 * b - 2 * a) * (3 * b - 2 * a) := by
  have h5 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hsq : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hbs : (0 : ℝ) ≤ b * Real.sqrt 5 := mul_nonneg hb h5
  constructor
  · intro h
    have hc : (b : ℝ) * Real.sqrt 5 < 3 * b - 2 * a := by linarith
    have hpos : (2 * a : ℝ) < 3 * b := by linarith
    have h1 : 2 * a < 3 * b := by exact_mod_cast hpos
    refine ⟨h1, ?_⟩
    have key : (5 : ℝ) * (b * b) < (3 * b - 2 * a) * (3 * b - 2 * a) := by
      have hprod : (b : ℝ) * Real.sqrt 5 * (b * Real.sqrt 5) = 5 * (b * b) := by
        rw [show (b : ℝ) * Real.sqrt 5 * (b * Real.sqrt 5) = b * b * (Real.sqrt 5 * Real.sqrt 5) by
          ring, hsq]
        ring
      nlinarith [mul_lt_mul'' hc hc hbs hbs]
    have hcast : ((5 * (b * b) : ℕ) : ℝ) < (((3 * b - 2 * a) * (3 * b - 2 * a) : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub h1.le]
      linarith
    exact_mod_cast hcast
  · rintro ⟨h1, h2⟩
    have hcast : ((5 * (b * b) : ℕ) : ℝ) < (((3 * b - 2 * a) * (3 * b - 2 * a) : ℕ) : ℝ) := by
      exact_mod_cast h2
    push_cast [Nat.cast_sub h1.le] at hcast
    have hpos : (2 * a : ℝ) < 3 * b := by exact_mod_cast h1
    have hc : (b : ℝ) * Real.sqrt 5 < 3 * b - 2 * a := by
      by_contra hle
      rw [not_lt] at hle
      have hnn : (0 : ℝ) ≤ 3 * b - 2 * a := by linarith
      have hprod : (b : ℝ) * Real.sqrt 5 * (b * Real.sqrt 5) = 5 * (b * b) := by
        rw [show (b : ℝ) * Real.sqrt 5 * (b * Real.sqrt 5) = b * b * (Real.sqrt 5 * Real.sqrt 5) by
          ring, hsq]
        ring
      nlinarith [mul_le_mul hle hle hnn hbs]
    linarith

/-- The decision of the cut of `(3 - √5)/2` on `n = Nat.pair a b`. -/
def fibCut (n : ℕ) : ℕ :=
  cond (decide (2 * (Nat.unpair n).1 < 3 * (Nat.unpair n).2) &&
    decide (5 * ((Nat.unpair n).2 * (Nat.unpair n).2) <
      (3 * (Nat.unpair n).2 - 2 * (Nat.unpair n).1) *
        (3 * (Nat.unpair n).2 - 2 * (Nat.unpair n).1))) 1 0

theorem primrec_fibCut : Primrec fibCut := by
  have ha : Primrec fun n : ℕ => (Nat.unpair n).1 := Primrec.fst.comp Primrec.unpair
  have hb : Primrec fun n : ℕ => (Nat.unpair n).2 := Primrec.snd.comp Primrec.unpair
  have h2a : Primrec fun n : ℕ => 2 * (Nat.unpair n).1 := Primrec.nat_mul.comp (Primrec.const 2) ha
  have h3b : Primrec fun n : ℕ => 3 * (Nat.unpair n).2 := Primrec.nat_mul.comp (Primrec.const 3) hb
  have hc : Primrec fun n : ℕ => 3 * (Nat.unpair n).2 - 2 * (Nat.unpair n).1 :=
    Primrec.nat_sub.comp h3b h2a
  exact (Primrec.cond (Primrec.and.comp (PrimrecPred.decide (Primrec.nat_lt.comp h2a h3b))
    (PrimrecPred.decide (Primrec.nat_lt.comp
      (Primrec.nat_mul.comp (Primrec.const 5) (Primrec.nat_mul.comp hb hb))
      (Primrec.nat_mul.comp hc hc)))) (Primrec.const 1) (Primrec.const 0)).of_eq fun _ => rfl

open Classical in
theorem fibCut_eq (n : ℕ) :
    fibCut n = if ((Nat.unpair n).1 : ℝ) < ((Nat.unpair n).2 : ℝ) * ((3 - Real.sqrt 5) / 2)
      then 1 else 0 := by
  simp only [fibCut, Bool.cond_eq_ite, Bool.and_eq_true, decide_eq_true_eq]
  by_cases h : ((Nat.unpair n).1 : ℝ) < ((Nat.unpair n).2 : ℝ) * ((3 - Real.sqrt 5) / 2)
  · rw [if_pos h, if_pos ((natCast_lt_mul_fibonacci_iff _ _).1 h)]
  · rw [if_neg h, if_neg fun hpq => h ((natCast_lt_mul_fibonacci_iff _ _).2 hpq)]

/-- The cut of `(3 - √5)/2` is computable. -/
theorem partrec_slopeOracle_fibonacci : Partrec (slopeOracle ((3 - Real.sqrt 5) / 2)) := by
  refine primrec_fibCut.to_comp.partrec.of_eq fun n => ?_
  show Part.some (fibCut n) = Part.some
    (if ((Nat.unpair n).1 : ℝ) < ((Nat.unpair n).2 : ℝ) * ((3 - Real.sqrt 5) / 2) then 1 else 0)
  rw [fibCut_eq]

theorem irrational_fibonacci_slope : Irrational ((3 - Real.sqrt 5) / 2) := by
  have hs5 : Irrational (Real.sqrt 5) := by simpa using Nat.prime_five.irrational_sqrt
  rintro ⟨q, hq⟩
  exact hs5 ⟨3 - 2 * q, by push_cast; rw [hq]; ring⟩

theorem fibonacci_slope_mem : 0 < (3 - Real.sqrt 5) / 2 ∧ (3 - Real.sqrt 5) / 2 < 1 := by
  have h5 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hsq : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  have hlt : Real.sqrt 5 < 3 := by nlinarith
  have hgt : 1 < Real.sqrt 5 := by nlinarith
  constructor <;> linarith

/-- **`cor:wp`, second sentence, "as for the Fibonacci subshift `X_{(3-√5)/2}`"**, from the one open
piece `L(X)` computes the word problem. -/
theorem printedFibonacciSolvableWordProblem_of (hc : PrintedWordProblemReducesToLanguage) :
    PrintedFibonacciSolvableWordProblem := by
  have hWL := hc Bool (sturmianSubshift ((3 - Real.sqrt 5) / 2))
  have hLα := printedSlopeComputesSturmianLanguage _ irrational_fibonacci_slope
    fibonacci_slope_mem.1 fibonacci_slope_mem.2
  exact partrec_iff_forall_turingReducible.2 fun _ =>
    (hWL.trans hLα).trans partrec_slopeOracle_fibonacci.turingReducible

#audit_axioms printedWordProblemDegreeEqLanguage_of
#audit_axioms printedSolvableWordProblemIffRecursiveLanguage_of
#audit_closed_axioms partrec_slopeOracle_fibonacci
#audit_axioms printedFibonacciSolvableWordProblem_of

end SimpleKazhdanSofic
end GroupApproximation
