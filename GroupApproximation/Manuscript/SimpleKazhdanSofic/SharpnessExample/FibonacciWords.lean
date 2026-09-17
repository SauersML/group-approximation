import GroupApproximation.Manuscript.SimpleKazhdanSofic.SturmianLanguageCriterion
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FiniteModelsLeastPeriod
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import GroupApproximation.Meta.AxiomGuard

/-!
# An example: the words of length three of the Fibonacci subshift

`simple_kazhdan_sofic_group.tex`, subsection "An example", l.409–412:

> Let $X$ be the Fibonacci subshift $X_{(3-\sqrt5)/2}$ of Corollary~\ref{cor:wp}. Its words of
> length~$3$ are $001$, $010$, $100$ and $101$. These are also the words of length~$3$ of the
> $5$-periodic sequence $y$ with $y_{[0,5)}=01001$, and no smaller period is possible.

* `fibonacciSubshift`: the Sturmian subshift `sturmianSubshift ((3 - √5)/2)` of the corpus (the
  subshift `X_α` of `cor:wp`).
* `manuscriptSentence_fibonacciWordsLengthThree` (l.410): its language in length `3` is
  `{001, 010, 100, 101}`. Route: the corpus criterion `mem_language_sturmianSubshift_iff_compare`
  (a word occurs iff `s_k - s_l - 1 < (k - l)α` for all `k, l ≤ n`, `s_k` the prefix counts of
  ones), with `1/3 < α < 1/2`. The four words pass all sixteen comparisons; `000` fails at
  `(k, l) = (0, 3)` (it needs `α < 1/3`), `011` at `(3, 1)` (it needs `α > 1/2`), and `110`, `111`
  at `(2, 0)` (they need `α > 1/2`).
* `fibonacciPeriodicWord`: `y_n = 1` iff `n ≡ 1, 4 (mod 5)`, so `y_{[0,5)} = 01001`.
* `manuscriptSentence_periodicWordsLengthThree` (l.411): `y` is `5`-periodic, its windows of
  length `3` are exactly the words of length `3` of `X`, its least period is `5`, and every
  sequence with period `p` and the same words of length `3` as `X` has `p ≥ 5`. The last point is
  local: an occurrence of `001` at `i` and of `101` at `j` rule out `p = 1, 2` at `i`, `p = 3` at
  `j + 2` (no `11`), and `p = 4` forces `000` at `i + 3`.
-/

namespace GroupApproximation.SimpleKazhdanSofic.SharpnessExample

open SymbolicDynamics.FullShift

/-- **The Fibonacci subshift** `X_{(3-√5)/2}` (tex l.409). -/
noncomputable def fibonacciSubshift : Subshift Bool ℤ :=
  sturmianSubshift ((3 - Real.sqrt 5) / 2)

theorem fibonacciSlope_bounds :
    1 / 3 < (3 - Real.sqrt 5) / 2 ∧ (3 - Real.sqrt 5) / 2 < 1 / 2 ∧ 0 < (3 - Real.sqrt 5) / 2 ∧
      (3 - Real.sqrt 5) / 2 < 1 := by
  have h5 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hsq : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  have hlt : Real.sqrt 5 < 7 / 3 := by nlinarith
  have hgt : 2 < Real.sqrt 5 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

section Members

theorem mem_language_001 :
    ![false, false, true] ∈ WordGraph.language fibonacciSubshift.carrier 3 := by
  obtain ⟨hlo, hhi, hpos, hlt1⟩ := fibonacciSlope_bounds
  refine (mem_language_sturmianSubshift_iff_compare _ hpos hlt1 _).2 ?_
  have h0 : (wordOnes ![false, false, true] 0 : ℝ) = 0 := by
    exact_mod_cast (by decide +kernel : wordOnes ![false, false, true] 0 = 0)
  have h1 : (wordOnes ![false, false, true] 1 : ℝ) = 0 := by
    exact_mod_cast (by decide +kernel : wordOnes ![false, false, true] 1 = 0)
  have h2 : (wordOnes ![false, false, true] 2 : ℝ) = 0 := by
    exact_mod_cast (by decide +kernel : wordOnes ![false, false, true] 2 = 0)
  have h3 : (wordOnes ![false, false, true] 3 : ℝ) = 1 := by
    exact_mod_cast (by decide +kernel : wordOnes ![false, false, true] 3 = 1)
  intro k l hk hl
  interval_cases k <;> interval_cases l <;> push_cast <;> linarith

theorem mem_language_010 :
    ![false, true, false] ∈ WordGraph.language fibonacciSubshift.carrier 3 := by
  obtain ⟨hlo, hhi, hpos, hlt1⟩ := fibonacciSlope_bounds
  refine (mem_language_sturmianSubshift_iff_compare _ hpos hlt1 _).2 ?_
  have h0 : (wordOnes ![false, true, false] 0 : ℝ) = 0 := by
    exact_mod_cast (by decide +kernel : wordOnes ![false, true, false] 0 = 0)
  have h1 : (wordOnes ![false, true, false] 1 : ℝ) = 0 := by
    exact_mod_cast (by decide +kernel : wordOnes ![false, true, false] 1 = 0)
  have h2 : (wordOnes ![false, true, false] 2 : ℝ) = 1 := by
    exact_mod_cast (by decide +kernel : wordOnes ![false, true, false] 2 = 1)
  have h3 : (wordOnes ![false, true, false] 3 : ℝ) = 1 := by
    exact_mod_cast (by decide +kernel : wordOnes ![false, true, false] 3 = 1)
  intro k l hk hl
  interval_cases k <;> interval_cases l <;> push_cast <;> linarith

theorem mem_language_100 :
    ![true, false, false] ∈ WordGraph.language fibonacciSubshift.carrier 3 := by
  obtain ⟨hlo, hhi, hpos, hlt1⟩ := fibonacciSlope_bounds
  refine (mem_language_sturmianSubshift_iff_compare _ hpos hlt1 _).2 ?_
  have h0 : (wordOnes ![true, false, false] 0 : ℝ) = 0 := by
    exact_mod_cast (by decide +kernel : wordOnes ![true, false, false] 0 = 0)
  have h1 : (wordOnes ![true, false, false] 1 : ℝ) = 1 := by
    exact_mod_cast (by decide +kernel : wordOnes ![true, false, false] 1 = 1)
  have h2 : (wordOnes ![true, false, false] 2 : ℝ) = 1 := by
    exact_mod_cast (by decide +kernel : wordOnes ![true, false, false] 2 = 1)
  have h3 : (wordOnes ![true, false, false] 3 : ℝ) = 1 := by
    exact_mod_cast (by decide +kernel : wordOnes ![true, false, false] 3 = 1)
  intro k l hk hl
  interval_cases k <;> interval_cases l <;> push_cast <;> linarith

theorem mem_language_101 :
    ![true, false, true] ∈ WordGraph.language fibonacciSubshift.carrier 3 := by
  obtain ⟨hlo, hhi, hpos, hlt1⟩ := fibonacciSlope_bounds
  refine (mem_language_sturmianSubshift_iff_compare _ hpos hlt1 _).2 ?_
  have h0 : (wordOnes ![true, false, true] 0 : ℝ) = 0 := by
    exact_mod_cast (by decide +kernel : wordOnes ![true, false, true] 0 = 0)
  have h1 : (wordOnes ![true, false, true] 1 : ℝ) = 1 := by
    exact_mod_cast (by decide +kernel : wordOnes ![true, false, true] 1 = 1)
  have h2 : (wordOnes ![true, false, true] 2 : ℝ) = 1 := by
    exact_mod_cast (by decide +kernel : wordOnes ![true, false, true] 2 = 1)
  have h3 : (wordOnes ![true, false, true] 3 : ℝ) = 2 := by
    exact_mod_cast (by decide +kernel : wordOnes ![true, false, true] 3 = 2)
  intro k l hk hl
  interval_cases k <;> interval_cases l <;> push_cast <;> linarith

end Members
