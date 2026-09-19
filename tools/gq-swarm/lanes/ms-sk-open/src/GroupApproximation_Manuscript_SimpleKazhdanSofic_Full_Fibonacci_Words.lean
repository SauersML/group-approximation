import GroupApproximation.Manuscript.SimpleKazhdanSofic.SturmianLanguageCriterion
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# The Fibonacci example: words of length three and the `5`-periodic sequence

`simple_kazhdan_sofic_group.tex`, subsection "An example" after the proof of `thm:main`,
l.409–412:

> Let $X$ be the Fibonacci subshift $X_{(3-\sqrt5)/2}$ of Corollary~\ref{cor:wp}. Its words of
> length~$3$ are $001$, $010$, $100$ and $101$. These are also the words of length~$3$ of the
> $5$-periodic sequence $y$ with $y_{[0,5)}=01001$, and no smaller period is possible.

* `fibonacciSubshift`: the Sturmian subshift `X_α`, `α = (3 - √5)/2`, of `cor:wp`.
* `fibonacciWordsLengthThree` (l.410): its words of length `3` are `001, 010, 100, 101`. Route: the
  finite criterion `SimpleKazhdanSofic.mem_language_sturmianSubshift_iff_compare` (a word occurs iff
  `s_k - s_l - 1 < (k - l)α` for all `k, l ≤ n`, `s_k` the prefix counts of ones) and
  `1/3 < α < 1/2`. The word `000` fails at `(0, 3)`, `011` at `(3, 1)`, `110` and `111` at `(2, 0)`.
* `fibonacciY`: `y_n = 1` iff `n ≡ 1, 4 (mod 5)`, so `y_{[0,5)} = 01001`.
* `fibonacciPeriodicWords` (l.411–412): `y` is `5`-periodic with the same words of length `3` as
  `X`, its least period (the minimal period under the shift) is `5`, and every sequence with a
  period `p > 0` and these words of length `3` has `p ≥ 5`.
-/

namespace GroupApproximation.Full.SK08

open SymbolicDynamics.FullShift

/-- **The Fibonacci subshift** `X_{(3-√5)/2}` (tex l.409). -/
noncomputable def fibonacciSubshift : Subshift Bool ℤ :=
  SimpleKazhdanSofic.sturmianSubshift ((3 - Real.sqrt 5) / 2)

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
  refine (SimpleKazhdanSofic.mem_language_sturmianSubshift_iff_compare _ hpos hlt1 _).2 ?_
  have h0 : (SimpleKazhdanSofic.wordOnes ![false, false, true] 0 : ℝ) = 0 := by
    exact_mod_cast (by decide +kernel : SimpleKazhdanSofic.wordOnes ![false, false, true] 0 = 0)
  have h1 : (SimpleKazhdanSofic.wordOnes ![false, false, true] 1 : ℝ) = 0 := by
    exact_mod_cast (by decide +kernel : SimpleKazhdanSofic.wordOnes ![false, false, true] 1 = 0)
  have h2 : (SimpleKazhdanSofic.wordOnes ![false, false, true] 2 : ℝ) = 0 := by
    exact_mod_cast (by decide +kernel : SimpleKazhdanSofic.wordOnes ![false, false, true] 2 = 0)
  have h3 : (SimpleKazhdanSofic.wordOnes ![false, false, true] 3 : ℝ) = 1 := by
    exact_mod_cast (by decide +kernel : SimpleKazhdanSofic.wordOnes ![false, false, true] 3 = 1)
  intro k l hk hl
  interval_cases k <;> interval_cases l <;> push_cast <;> linarith [hlo, hhi, h0, h1, h2, h3]

theorem mem_language_010 :
    ![false, true, false] ∈ WordGraph.language fibonacciSubshift.carrier 3 := by
  obtain ⟨hlo, hhi, hpos, hlt1⟩ := fibonacciSlope_bounds
  refine (SimpleKazhdanSofic.mem_language_sturmianSubshift_iff_compare _ hpos hlt1 _).2 ?_
  have h0 : (SimpleKazhdanSofic.wordOnes ![false, true, false] 0 : ℝ) = 0 := by
    exact_mod_cast (by decide +kernel : SimpleKazhdanSofic.wordOnes ![false, true, false] 0 = 0)
  have h1 : (SimpleKazhdanSofic.wordOnes ![false, true, false] 1 : ℝ) = 0 := by
    exact_mod_cast (by decide +kernel : SimpleKazhdanSofic.wordOnes ![false, true, false] 1 = 0)
  have h2 : (SimpleKazhdanSofic.wordOnes ![false, true, false] 2 : ℝ) = 1 := by
    exact_mod_cast (by decide +kernel : SimpleKazhdanSofic.wordOnes ![false, true, false] 2 = 1)
  have h3 : (SimpleKazhdanSofic.wordOnes ![false, true, false] 3 : ℝ) = 1 := by
    exact_mod_cast (by decide +kernel : SimpleKazhdanSofic.wordOnes ![false, true, false] 3 = 1)
  intro k l hk hl
  interval_cases k <;> interval_cases l <;> push_cast <;> linarith [hlo, hhi, h0, h1, h2, h3]

theorem mem_language_100 :
    ![true, false, false] ∈ WordGraph.language fibonacciSubshift.carrier 3 := by
  obtain ⟨hlo, hhi, hpos, hlt1⟩ := fibonacciSlope_bounds
  refine (SimpleKazhdanSofic.mem_language_sturmianSubshift_iff_compare _ hpos hlt1 _).2 ?_
  have h0 : (SimpleKazhdanSofic.wordOnes ![true, false, false] 0 : ℝ) = 0 := by
    exact_mod_cast (by decide +kernel : SimpleKazhdanSofic.wordOnes ![true, false, false] 0 = 0)
  have h1 : (SimpleKazhdanSofic.wordOnes ![true, false, false] 1 : ℝ) = 1 := by
    exact_mod_cast (by decide +kernel : SimpleKazhdanSofic.wordOnes ![true, false, false] 1 = 1)
  have h2 : (SimpleKazhdanSofic.wordOnes ![true, false, false] 2 : ℝ) = 1 := by
    exact_mod_cast (by decide +kernel : SimpleKazhdanSofic.wordOnes ![true, false, false] 2 = 1)
  have h3 : (SimpleKazhdanSofic.wordOnes ![true, false, false] 3 : ℝ) = 1 := by
    exact_mod_cast (by decide +kernel : SimpleKazhdanSofic.wordOnes ![true, false, false] 3 = 1)
  intro k l hk hl
  interval_cases k <;> interval_cases l <;> push_cast <;> linarith [hlo, hhi, h0, h1, h2, h3]

theorem mem_language_101 :
    ![true, false, true] ∈ WordGraph.language fibonacciSubshift.carrier 3 := by
  obtain ⟨hlo, hhi, hpos, hlt1⟩ := fibonacciSlope_bounds
  refine (SimpleKazhdanSofic.mem_language_sturmianSubshift_iff_compare _ hpos hlt1 _).2 ?_
  have h0 : (SimpleKazhdanSofic.wordOnes ![true, false, true] 0 : ℝ) = 0 := by
    exact_mod_cast (by decide +kernel : SimpleKazhdanSofic.wordOnes ![true, false, true] 0 = 0)
  have h1 : (SimpleKazhdanSofic.wordOnes ![true, false, true] 1 : ℝ) = 1 := by
    exact_mod_cast (by decide +kernel : SimpleKazhdanSofic.wordOnes ![true, false, true] 1 = 1)
  have h2 : (SimpleKazhdanSofic.wordOnes ![true, false, true] 2 : ℝ) = 1 := by
    exact_mod_cast (by decide +kernel : SimpleKazhdanSofic.wordOnes ![true, false, true] 2 = 1)
  have h3 : (SimpleKazhdanSofic.wordOnes ![true, false, true] 3 : ℝ) = 2 := by
    exact_mod_cast (by decide +kernel : SimpleKazhdanSofic.wordOnes ![true, false, true] 3 = 2)
  intro k l hk hl
  interval_cases k <;> interval_cases l <;> push_cast <;> linarith [hlo, hhi, h0, h1, h2, h3]

end Members

section NonMembers

/-- `000` would need `3α < 1`. -/
theorem not_mem_language_000 :
    ![false, false, false] ∉ WordGraph.language fibonacciSubshift.carrier 3 := by
  obtain ⟨hlo, -, hpos, hlt1⟩ := fibonacciSlope_bounds
  intro h
  have hk := (SimpleKazhdanSofic.mem_language_sturmianSubshift_iff_compare _ hpos hlt1 _).1 h 0 3
    (by norm_num) (by norm_num)
  have h0 : (SimpleKazhdanSofic.wordOnes ![false, false, false] 0 : ℝ) = 0 := by
    exact_mod_cast (by decide +kernel : SimpleKazhdanSofic.wordOnes ![false, false, false] 0 = 0)
  have h3 : (SimpleKazhdanSofic.wordOnes ![false, false, false] 3 : ℝ) = 0 := by
    exact_mod_cast (by decide +kernel : SimpleKazhdanSofic.wordOnes ![false, false, false] 3 = 0)
  push_cast at hk
  linarith [hlo, h0, h3, hk]

/-- `011` would need `2α > 1`. -/
theorem not_mem_language_011 :
    ![false, true, true] ∉ WordGraph.language fibonacciSubshift.carrier 3 := by
  obtain ⟨-, hhi, hpos, hlt1⟩ := fibonacciSlope_bounds
  intro h
  have hk := (SimpleKazhdanSofic.mem_language_sturmianSubshift_iff_compare _ hpos hlt1 _).1 h 3 1
    (by norm_num) (by norm_num)
  have h1 : (SimpleKazhdanSofic.wordOnes ![false, true, true] 1 : ℝ) = 0 := by
    exact_mod_cast (by decide +kernel : SimpleKazhdanSofic.wordOnes ![false, true, true] 1 = 0)
  have h3 : (SimpleKazhdanSofic.wordOnes ![false, true, true] 3 : ℝ) = 2 := by
    exact_mod_cast (by decide +kernel : SimpleKazhdanSofic.wordOnes ![false, true, true] 3 = 2)
  push_cast at hk
  linarith [hhi, h1, h3, hk]

/-- `110` would need `2α > 1`. -/
theorem not_mem_language_110 :
    ![true, true, false] ∉ WordGraph.language fibonacciSubshift.carrier 3 := by
  obtain ⟨-, hhi, hpos, hlt1⟩ := fibonacciSlope_bounds
  intro h
  have hk := (SimpleKazhdanSofic.mem_language_sturmianSubshift_iff_compare _ hpos hlt1 _).1 h 2 0
    (by norm_num) (by norm_num)
  have h0 : (SimpleKazhdanSofic.wordOnes ![true, true, false] 0 : ℝ) = 0 := by
    exact_mod_cast (by decide +kernel : SimpleKazhdanSofic.wordOnes ![true, true, false] 0 = 0)
  have h2 : (SimpleKazhdanSofic.wordOnes ![true, true, false] 2 : ℝ) = 2 := by
    exact_mod_cast (by decide +kernel : SimpleKazhdanSofic.wordOnes ![true, true, false] 2 = 2)
  push_cast at hk
  linarith [hhi, h0, h2, hk]

/-- `111` would need `2α > 1`. -/
theorem not_mem_language_111 :
    ![true, true, true] ∉ WordGraph.language fibonacciSubshift.carrier 3 := by
  obtain ⟨-, hhi, hpos, hlt1⟩ := fibonacciSlope_bounds
  intro h
  have hk := (SimpleKazhdanSofic.mem_language_sturmianSubshift_iff_compare _ hpos hlt1 _).1 h 2 0
    (by norm_num) (by norm_num)
  have h0 : (SimpleKazhdanSofic.wordOnes ![true, true, true] 0 : ℝ) = 0 := by
    exact_mod_cast (by decide +kernel : SimpleKazhdanSofic.wordOnes ![true, true, true] 0 = 0)
  have h2 : (SimpleKazhdanSofic.wordOnes ![true, true, true] 2 : ℝ) = 2 := by
    exact_mod_cast (by decide +kernel : SimpleKazhdanSofic.wordOnes ![true, true, true] 2 = 2)
  push_cast at hk
  linarith [hhi, h0, h2, hk]

end NonMembers

/-- **tex l.409–410.** The words of length `3` of the Fibonacci subshift `X_{(3-√5)/2}` are `001`,
`010`, `100` and `101`. -/
theorem fibonacciWordsLengthThree :
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

#audit_closed_axioms fibonacciWordsLengthThree

section Periodic

/-- **The `5`-periodic sequence `y`** with `y_{[0,5)} = 01001` (tex l.411): `y_n = 1` iff
`n ≡ 1` or `n ≡ 4 (mod 5)`. -/
def fibonacciY (n : ℤ) : Bool :=
  decide (n % 5 = 1 ∨ n % 5 = 4)

theorem word_fibonacciY_zero_five :
    WordGraph.word fibonacciY 0 5 = ![false, true, false, false, true] := by
  decide +kernel

theorem fibonacciY_add_five (n : ℤ) : fibonacciY ((5 : ℕ) + n) = fibonacciY n := by
  unfold fibonacciY
  rw [decide_eq_decide]
  omega

theorem word_fibonacciY_emod (i : ℤ) :
    WordGraph.word fibonacciY i 3 = WordGraph.word fibonacciY (i % 5) 3 := by
  funext j
  rw [WordGraph.word_apply, WordGraph.word_apply]
  unfold fibonacciY
  rw [decide_eq_decide]
  omega

/-- The windows of length `3` of `y` are `001`, `010`, `100`, `101` (at `2`, `0`, `1`, `4`). -/
theorem range_word_fibonacciY :
    Set.range (fun i : ℤ => WordGraph.word fibonacciY i 3) =
      {![false, false, true], ![false, true, false], ![true, false, false],
        ![true, false, true]} := by
  ext w
  rw [Set.mem_range, Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    show WordGraph.word fibonacciY i 3 = _ ∨ _
    rw [word_fibonacciY_emod]
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

theorem iterate_shift_one_apply (p : ℕ) (z : ℤ → Bool) (t : ℤ) :
    (shift (1 : ℤ))^[p] z t = z (p + t) := by
  induction p generalizing t with
  | zero =>
    rw [Function.iterate_zero_apply, Nat.cast_zero, zero_add]
  | succ p ih =>
    rw [Function.iterate_succ_apply', shift_apply, ih]
    congr 1
    omega

theorem isPeriodicPt_shift_iff' (z : ℤ → Bool) (p : ℕ) :
    Function.IsPeriodicPt (shift (1 : ℤ)) p z ↔ ∀ t : ℤ, z (p + t) = z t := by
  constructor
  · intro h t
    have ht : (shift (1 : ℤ))^[p] z t = z t := congrFun (show (shift (1 : ℤ))^[p] z = z from h) t
    rw [iterate_shift_one_apply] at ht
    exact ht
  · intro h
    show (shift (1 : ℤ))^[p] z = z
    funext t
    rw [iterate_shift_one_apply]
    exact h t

/-- **The least period of `y` is `5`**: `5` is a period, the minimal period divides the prime `5`,
and `y` is not constant. -/
theorem minimalPeriod_fibonacciY : Function.minimalPeriod (shift (1 : ℤ)) fibonacciY = 5 := by
  have hper : Function.IsPeriodicPt (shift (1 : ℤ)) 5 fibonacciY :=
    (isPeriodicPt_shift_iff' _ 5).2 fibonacciY_add_five
  rcases Nat.prime_five.eq_one_or_self_of_dvd _ hper.minimalPeriod_dvd with h1 | h1
  · have hp := (isPeriodicPt_shift_iff' _ _).1
      (Function.isPeriodicPt_minimalPeriod (shift (1 : ℤ)) fibonacciY) 0
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

/-- **No smaller period is possible** (tex l.412): a sequence with a period `p > 0` whose words of
length `3` are those of `X` has `p ≥ 5`. -/
theorem five_le_of_periodic_words (z : ℤ → Bool) (p : ℕ) (hp : 0 < p)
    (hper : ∀ n : ℤ, z (p + n) = z n)
    (hwords : Set.range (fun i : ℤ => WordGraph.word z i 3) =
      WordGraph.language fibonacciSubshift.carrier 3) :
    5 ≤ p := by
  rw [fibonacciWordsLengthThree] at hwords
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

#audit_axioms five_le_of_periodic_words

end NoSmallerPeriod

/-- **tex l.410–412.** The `5`-periodic sequence `y` with `y_{[0,5)} = 01001` has the same words of
length `3` as the Fibonacci subshift, its least period is `5`, and no smaller period is possible
for a sequence with these words of length `3`. -/
theorem fibonacciPeriodicWords :
    WordGraph.word fibonacciY 0 5 = ![false, true, false, false, true] ∧
      (∀ n : ℤ, fibonacciY ((5 : ℕ) + n) = fibonacciY n) ∧
      Set.range (fun i : ℤ => WordGraph.word fibonacciY i 3) =
        WordGraph.language fibonacciSubshift.carrier 3 ∧
      Function.minimalPeriod (shift (1 : ℤ)) fibonacciY = 5 ∧
      ∀ (z : ℤ → Bool) (p : ℕ), 0 < p → (∀ n : ℤ, z (p + n) = z n) →
        Set.range (fun i : ℤ => WordGraph.word z i 3) =
          WordGraph.language fibonacciSubshift.carrier 3 → 5 ≤ p := by
  refine ⟨word_fibonacciY_zero_five, fibonacciY_add_five, ?_, minimalPeriod_fibonacciY,
    five_le_of_periodic_words⟩
  rw [range_word_fibonacciY, fibonacciWordsLengthThree]

#audit_closed_axioms fibonacciPeriodicWords

end GroupApproximation.Full.SK08
