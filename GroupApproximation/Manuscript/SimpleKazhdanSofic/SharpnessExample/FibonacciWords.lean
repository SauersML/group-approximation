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
  interval_cases k <;> interval_cases l <;> push_cast <;> linarith [hlo, hhi, h0, h1, h2, h3]

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
  interval_cases k <;> interval_cases l <;> push_cast <;> linarith [hlo, hhi, h0, h1, h2, h3]

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
  interval_cases k <;> interval_cases l <;> push_cast <;> linarith [hlo, hhi, h0, h1, h2, h3]

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
  interval_cases k <;> interval_cases l <;> push_cast <;> linarith [hlo, hhi, h0, h1, h2, h3]

end Members

section NonMembers

/-- `000` would need `3α < 1`. -/
theorem not_mem_language_000 :
    ![false, false, false] ∉ WordGraph.language fibonacciSubshift.carrier 3 := by
  obtain ⟨hlo, -, hpos, hlt1⟩ := fibonacciSlope_bounds
  intro h
  have hk := (mem_language_sturmianSubshift_iff_compare _ hpos hlt1 _).1 h 0 3 (by norm_num)
    (by norm_num)
  have h0 : (wordOnes ![false, false, false] 0 : ℝ) = 0 := by
    exact_mod_cast (by decide +kernel : wordOnes ![false, false, false] 0 = 0)
  have h3 : (wordOnes ![false, false, false] 3 : ℝ) = 0 := by
    exact_mod_cast (by decide +kernel : wordOnes ![false, false, false] 3 = 0)
  push_cast at hk
  linarith [hlo, h0, h3, hk]

/-- `011` would need `2α > 1`. -/
theorem not_mem_language_011 :
    ![false, true, true] ∉ WordGraph.language fibonacciSubshift.carrier 3 := by
  obtain ⟨-, hhi, hpos, hlt1⟩ := fibonacciSlope_bounds
  intro h
  have hk := (mem_language_sturmianSubshift_iff_compare _ hpos hlt1 _).1 h 3 1 (by norm_num)
    (by norm_num)
  have h1 : (wordOnes ![false, true, true] 1 : ℝ) = 0 := by
    exact_mod_cast (by decide +kernel : wordOnes ![false, true, true] 1 = 0)
  have h3 : (wordOnes ![false, true, true] 3 : ℝ) = 2 := by
    exact_mod_cast (by decide +kernel : wordOnes ![false, true, true] 3 = 2)
  push_cast at hk
  linarith [hhi, h1, h3, hk]

/-- `110` would need `2α > 1`. -/
theorem not_mem_language_110 :
    ![true, true, false] ∉ WordGraph.language fibonacciSubshift.carrier 3 := by
  obtain ⟨-, hhi, hpos, hlt1⟩ := fibonacciSlope_bounds
  intro h
  have hk := (mem_language_sturmianSubshift_iff_compare _ hpos hlt1 _).1 h 2 0 (by norm_num)
    (by norm_num)
  have h0 : (wordOnes ![true, true, false] 0 : ℝ) = 0 := by
    exact_mod_cast (by decide +kernel : wordOnes ![true, true, false] 0 = 0)
  have h2 : (wordOnes ![true, true, false] 2 : ℝ) = 2 := by
    exact_mod_cast (by decide +kernel : wordOnes ![true, true, false] 2 = 2)
  push_cast at hk
  linarith [hhi, h0, h2, hk]

/-- `111` would need `2α > 1`. -/
theorem not_mem_language_111 :
    ![true, true, true] ∉ WordGraph.language fibonacciSubshift.carrier 3 := by
  obtain ⟨-, hhi, hpos, hlt1⟩ := fibonacciSlope_bounds
  intro h
  have hk := (mem_language_sturmianSubshift_iff_compare _ hpos hlt1 _).1 h 2 0 (by norm_num)
    (by norm_num)
  have h0 : (wordOnes ![true, true, true] 0 : ℝ) = 0 := by
    exact_mod_cast (by decide +kernel : wordOnes ![true, true, true] 0 = 0)
  have h2 : (wordOnes ![true, true, true] 2 : ℝ) = 2 := by
    exact_mod_cast (by decide +kernel : wordOnes ![true, true, true] 2 = 2)
  push_cast at hk
  linarith [hhi, h0, h2, hk]

end NonMembers

/-- **Sentence l.410 (tex l.409–410).** The words of length `3` of the Fibonacci subshift
`X_{(3-√5)/2}` are `001`, `010`, `100` and `101`. -/
theorem manuscriptSentence_fibonacciWordsLengthThree :
    WordGraph.language fibonacciSubshift.carrier 3 =
      {![false, false, true], ![false, true, false], ![true, false, false],
        ![true, false, true]} := by
  ext w
  rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c : Bool, w = ![a, b, c] :=
    ⟨w 0, w 1, w 2, by funext i; fin_cases i <;> rfl⟩
  cases a <;> cases b <;> cases c
  · exact iff_of_false not_mem_language_000 (by decide +kernel)
  · exact iff_of_true mem_language_001 (Or.inl rfl)
  · exact iff_of_true mem_language_010 (Or.inr (Or.inl rfl))
  · exact iff_of_false not_mem_language_011 (by decide +kernel)
  · exact iff_of_true mem_language_100 (Or.inr (Or.inr (Or.inl rfl)))
  · exact iff_of_true mem_language_101 (Or.inr (Or.inr (Or.inr rfl)))
  · exact iff_of_false not_mem_language_110 (by decide +kernel)
  · exact iff_of_false not_mem_language_111 (by decide +kernel)

#audit_axioms manuscriptSentence_fibonacciWordsLengthThree

section Periodic

/-- **The `5`-periodic sequence `y`** with `y_{[0,5)} = 01001` (tex l.411): `y_n = 1` iff
`n ≡ 1` or `n ≡ 4 (mod 5)`. -/
def fibonacciPeriodicWord (n : ℤ) : Bool :=
  decide (n % 5 = 1 ∨ n % 5 = 4)

theorem word_fibonacciPeriodicWord_zero_five :
    WordGraph.word fibonacciPeriodicWord 0 5 = ![false, true, false, false, true] := by
  decide +kernel

theorem fibonacciPeriodicWord_add_five (n : ℤ) :
    fibonacciPeriodicWord ((5 : ℕ) + n) = fibonacciPeriodicWord n := by
  unfold fibonacciPeriodicWord
  rw [decide_eq_decide]
  omega

theorem word_fibonacciPeriodicWord_emod (i : ℤ) :
    WordGraph.word fibonacciPeriodicWord i 3 = WordGraph.word fibonacciPeriodicWord (i % 5) 3 := by
  funext j
  rw [WordGraph.word_apply, WordGraph.word_apply]
  unfold fibonacciPeriodicWord
  rw [decide_eq_decide]
  omega

/-- The windows of length `3` of `y` are `001`, `010`, `100`, `101`: those at `2`, `0` (and `3`),
`1` and `4`. -/
theorem range_word_fibonacciPeriodicWord :
    Set.range (fun i : ℤ => WordGraph.word fibonacciPeriodicWord i 3) =
      {![false, false, true], ![false, true, false], ![true, false, false],
        ![true, false, true]} := by
  ext w
  rw [Set.mem_range, Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    show WordGraph.word fibonacciPeriodicWord i 3 = _ ∨ _
    rw [word_fibonacciPeriodicWord_emod]
    have h0 : 0 ≤ i % 5 := Int.emod_nonneg i (by norm_num)
    have h5 : i % 5 < 5 := Int.emod_lt_of_pos i (by norm_num)
    obtain ⟨r, hr⟩ : ∃ r : ℤ, i % 5 = r := ⟨_, rfl⟩
    rw [hr] at h0 h5 ⊢
    interval_cases r <;> decide +kernel
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨2, by decide +kernel⟩
    · exact ⟨0, by decide +kernel⟩
    · exact ⟨1, by decide +kernel⟩
    · exact ⟨4, by decide +kernel⟩

/-- The least period of `y` is `5`: it divides `5` and `y` is not constant. -/
theorem leastPeriod_fibonacciPeriodicWord : leastPeriod fibonacciPeriodicWord = 5 := by
  have hper : Function.IsPeriodicPt (shift (1 : ℤ)) 5 fibonacciPeriodicWord :=
    (isPeriodicPt_shift_iff _ 5).2 fibonacciPeriodicWord_add_five
  rcases Nat.prime_five.eq_one_or_self_of_dvd _ hper.minimalPeriod_dvd with h1 | h1
  · have hp := (isPeriodicPt_shift_iff _ _).1
      (Function.isPeriodicPt_minimalPeriod (shift (1 : ℤ)) fibonacciPeriodicWord) 0
    rw [h1] at hp
    exact absurd hp (by decide +kernel)
  · exact h1

end Periodic

section NoSmallerPeriod

theorem word_three_letters {z : ℤ → Bool} {k : ℤ} {w : Fin 3 → Bool}
    (h : WordGraph.word z k 3 = w) : z k = w 0 ∧ z (k + 1) = w 1 ∧ z (k + 2) = w 2 := by
  have h0 : z (k + 0) = w 0 := congrFun h 0
  have h1 : z (k + 1) = w 1 := congrFun h 1
  have h2 : z (k + 2) = w 2 := congrFun h 2
  rw [add_zero] at h0
  exact ⟨h0, h1, h2⟩

/-- A window equal to one of `001`, `010`, `100`, `101` contains no `11` and is not `000`. -/
theorem letters_of_word_mem {z : ℤ → Bool} {k : ℤ}
    (h : WordGraph.word z k 3 = ![false, false, true] ∨
      WordGraph.word z k 3 = ![false, true, false] ∨
      WordGraph.word z k 3 = ![true, false, false] ∨ WordGraph.word z k 3 = ![true, false, true]) :
    (z k = false ∨ z (k + 1) = false) ∧ (z (k + 1) = false ∨ z (k + 2) = false) ∧
      (z k = true ∨ z (k + 1) = true ∨ z (k + 2) = true) := by
  rcases h with h | h | h | h <;> obtain ⟨h0, h1, h2⟩ := word_three_letters h <;>
    rw [h0, h1, h2] <;> decide +kernel

/-- **No smaller period is possible** (tex l.411): a sequence with period `p > 0` whose words of
length `3` are those of `X` has `p ≥ 5`. -/
theorem five_le_of_periodic_words (z : ℤ → Bool) (p : ℕ) (hp : 0 < p)
    (hper : ∀ n : ℤ, z (p + n) = z n)
    (hwords : Set.range (fun i : ℤ => WordGraph.word z i 3) =
      WordGraph.language fibonacciSubshift.carrier 3) :
    5 ≤ p := by
  rw [manuscriptSentence_fibonacciWordsLengthThree] at hwords
  have hletters : ∀ k : ℤ, (z k = false ∨ z (k + 1) = false) ∧
      (z (k + 1) = false ∨ z (k + 2) = false) ∧
      (z k = true ∨ z (k + 1) = true ∨ z (k + 2) = true) := by
    intro k
    have hk : WordGraph.word z k 3 ∈ Set.range (fun i : ℤ => WordGraph.word z i 3) :=
      Set.mem_range_self k
    rw [hwords, Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hk
    exact letters_of_word_mem hk
  have hz : ∀ a b : ℤ, a = b + p → z a = z b := by
    intro a b hab
    rw [hab, add_comm]
    exact hper b
  have h001 : ![false, false, true] ∈ Set.range (fun i : ℤ => WordGraph.word z i 3) := by
    rw [hwords]
    exact Set.mem_insert _ _
  have h101 : ![true, false, true] ∈ Set.range (fun i : ℤ => WordGraph.word z i 3) := by
    rw [hwords]
    exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  obtain ⟨i, hi⟩ := h001
  obtain ⟨j, hj⟩ := h101
  have a0 : z i = false := (word_three_letters hi).1
  have a1 : z (i + 1) = false := (word_three_letters hi).2.1
  have a2 : z (i + 2) = true := (word_three_letters hi).2.2
  have b0 : z j = true := (word_three_letters hj).1
  have b2 : z (j + 2) = true := (word_three_letters hj).2.2
  by_contra hlt
  have hle : p ≤ 4 := by omega
  interval_cases p
  · exact absurd ((a2.symm.trans (hz (i + 2) (i + 1) (by omega))).trans a1) (by decide)
  · exact absurd ((a2.symm.trans (hz (i + 2) i (by omega))).trans a0) (by decide)
  · have e3 : z (j + 2 + 1) = true := (hz (j + 2 + 1) j (by omega)).trans b0
    rcases (hletters (j + 2)).1 with h | h
    · exact absurd (b2.symm.trans h) (by decide)
    · exact absurd (e3.symm.trans h) (by decide)
  · have e1 : z (i + 2 + 1) = false := by
      rcases (hletters (i + 2)).1 with h | h
      · exact absurd (a2.symm.trans h) (by decide)
      · exact h
    have e4 : z (i + 2 + 1 + 1) = false := (hz (i + 2 + 1 + 1) i (by omega)).trans a0
    have e5 : z (i + 2 + 1 + 2) = false := (hz (i + 2 + 1 + 2) (i + 1) (by omega)).trans a1
    rcases (hletters (i + 2 + 1)).2.2 with h | h | h
    · exact absurd (e1.symm.trans h) (by decide)
    · exact absurd (e4.symm.trans h) (by decide)
    · exact absurd (e5.symm.trans h) (by decide)

end NoSmallerPeriod

/-- **Sentence l.411 (tex l.410–412).** The `5`-periodic sequence `y` with `y_{[0,5)} = 01001` has
the same words of length `3` as the Fibonacci subshift, its least period is `5`, and no smaller
period is possible for a sequence with these words. -/
theorem manuscriptSentence_periodicWordsLengthThree :
    WordGraph.word fibonacciPeriodicWord 0 5 = ![false, true, false, false, true] ∧
      (∀ n : ℤ, fibonacciPeriodicWord ((5 : ℕ) + n) = fibonacciPeriodicWord n) ∧
      Set.range (fun i : ℤ => WordGraph.word fibonacciPeriodicWord i 3) =
        WordGraph.language fibonacciSubshift.carrier 3 ∧
      leastPeriod fibonacciPeriodicWord = 5 ∧
      ∀ (z : ℤ → Bool) (p : ℕ), 0 < p → (∀ n : ℤ, z (p + n) = z n) →
        Set.range (fun i : ℤ => WordGraph.word z i 3) =
          WordGraph.language fibonacciSubshift.carrier 3 → 5 ≤ p := by
  refine ⟨word_fibonacciPeriodicWord_zero_five, fibonacciPeriodicWord_add_five, ?_,
    leastPeriod_fibonacciPeriodicWord, five_le_of_periodic_words⟩
  rw [range_word_fibonacciPeriodicWord, manuscriptSentence_fibonacciWordsLengthThree]

#audit_axioms manuscriptSentence_periodicWordsLengthThree

end GroupApproximation.SimpleKazhdanSofic.SharpnessExample
