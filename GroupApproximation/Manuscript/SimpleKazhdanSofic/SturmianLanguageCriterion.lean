import GroupApproximation.Manuscript.SimpleKazhdanSofic.SturmianLanguage
import GroupApproximation.Meta.AxiomGuard

/-!
# Sturmian words by comparisons of the slope with rationals

`simple_kazhdan_sofic_group.tex` (origin/main e80dcf20a), proof of the corollary in "Word problems",
tex l.268–271:

> So $\alpha$ computes $L(X_\alpha)$. Since
> $c(\theta)_t=\lfloor\theta+(t+1)\alpha\rfloor-\lfloor\theta+t\alpha\rfloor$, the word
> $c(\theta)_{[0,n)}$ has $\lfloor\theta+n\alpha\rfloor$ ones, within $1$ of $n\alpha$, so
> $L(X_\alpha)$ computes $\alpha$.

Both reductions in `SturmianComputability` rest on two finite criteria.
* `mem_language_sturmianSubshift_iff_compare`: write `s_k` for the number of ones among the first
  `k` letters of `w`. A word `w` of length `n` occurs in `X_α` exactly when
  `s_k - s_l - 1 < (k - l)α` for all `k, l ≤ n`. Then `w = c(θ)_{[0,n)}` for
  `θ = max_k (s_k - kα)`, because `s_k = ⌊θ + kα⌋`. So membership is decided by finitely many
  comparisons of `α` with rationals.
* `intCast_lt_mul_iff_forall_mem_language`: for irrational `α` and `b ≥ 1`, `a < bα` exactly when
  every word of length `b` of `X_α` has at least `a` ones. The word `c(θ)_{[0,b)}` has
  `⌊θ + bα⌋ - ⌊θ⌋ ≥ ⌊bα⌋` ones, with equality at `θ = 0`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

/-- The number of ones among the first `k` letters of a word `w` of length `n`; letters past `n`
count as `0`. -/
def wordOnes {n : ℕ} (w : Fin n → Bool) (k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range k, if h : j < n then (if w ⟨j, h⟩ then 1 else 0) else 0

theorem wordOnes_succ {n : ℕ} (w : Fin n → Bool) (t : Fin n) :
    wordOnes w ((t : ℕ) + 1) = wordOnes w t + (if w t then 1 else 0) := by
  unfold wordOnes
  rw [Finset.sum_range_succ, dif_pos t.2]

/-- The prefix counts of a coding word are floor differences. -/
theorem wordOnes_word_sturmianCoding (α θ : ℝ) (hα0 : 0 < α) (hα1 : α < 1) {n k : ℕ}
    (hk : k ≤ n) :
    wordOnes (WordGraph.word (sturmianCoding α θ) 0 n) k = ⌊θ + (k : ℝ) * α⌋ - ⌊θ⌋ := by
  rw [← sum_sturmianCoding α θ hα0 hα1 k]
  unfold wordOnes
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [dif_pos (lt_of_lt_of_le (Finset.mem_range.mp hj) hk)]
  simp only [WordGraph.word_apply, zero_add]

theorem bool_eq_of_indicator_eq {a b : Bool}
    (h : (if a then (1 : ℤ) else 0) = (if b then 1 else 0)) : a = b := by
  cases a <;> cases b <;> simp_all

/-- A word occurs in the Sturmian subshift exactly when its prefix counts satisfy finitely many
strict comparisons with multiples of `α`. -/
theorem mem_language_sturmianSubshift_iff_compare (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) {n : ℕ}
    (w : Fin n → Bool) :
    w ∈ WordGraph.language (sturmianSubshift α).carrier n ↔
      ∀ k l : ℕ, k ≤ n → l ≤ n → (wordOnes w k : ℝ) - wordOnes w l - 1 < ((k : ℝ) - l) * α := by
  rw [language_sturmianSubshift]
  constructor
  · rintro ⟨θ, rfl⟩ k l hk hl
    rw [wordOnes_word_sturmianCoding α θ hα0 hα1 hk, wordOnes_word_sturmianCoding α θ hα0 hα1 hl]
    have h1 := Int.floor_le (θ + (k : ℝ) * α)
    have h2 := Int.lt_floor_add_one (θ + (l : ℝ) * α)
    push_cast
    linarith
  · intro h
    obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (Finset.range (n + 1))
      (fun k : ℕ => (wordOnes w k : ℝ) - (k : ℝ) * α) ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
    have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hfloor : ∀ k : ℕ, k ≤ n →
        ⌊(wordOnes w m : ℝ) - (m : ℝ) * α + (k : ℝ) * α⌋ = wordOnes w k := by
      intro k hk
      rw [Int.floor_eq_iff]
      have hk' : (wordOnes w k : ℝ) - (k : ℝ) * α ≤ (wordOnes w m : ℝ) - (m : ℝ) * α :=
        hmax k (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
      have hmk := h m k hmn hk
      constructor <;> linarith
    refine ⟨(wordOnes w m : ℝ) - (m : ℝ) * α, ?_⟩
    funext t
    have e1 := sturmianCoding_eq_floor_sub α ((wordOnes w m : ℝ) - (m : ℝ) * α) hα0 hα1
      ((t : ℕ) : ℤ)
    have e2 := hfloor t (le_of_lt t.2)
    have e3 := hfloor ((t : ℕ) + 1) (Nat.succ_le_of_lt t.2)
    have e4 := wordOnes_succ w t
    push_cast at e1 e3
    have key : (if sturmianCoding α ((wordOnes w m : ℝ) - (m : ℝ) * α) ((t : ℕ) : ℤ) then (1 : ℤ)
        else 0) = (if w t then 1 else 0) := by
      linarith
    simp only [WordGraph.word_apply, zero_add]
    exact bool_eq_of_indicator_eq key

/-- For irrational `α` and `b ≥ 1`, `a < bα` exactly when every word of length `b` of the Sturmian
subshift has at least `a` ones. -/
theorem intCast_lt_mul_iff_forall_mem_language (α : ℝ) (hα : Irrational α) (hα0 : 0 < α)
    (hα1 : α < 1) (a : ℤ) {b : ℕ} (hb : 0 < b) :
    (a : ℝ) < (b : ℝ) * α ↔
      ∀ w : Fin b → Bool, w ∈ WordGraph.language (sturmianSubshift α).carrier b →
        a ≤ wordOnes w b := by
  rw [language_sturmianSubshift]
  constructor
  · rintro h w ⟨θ, rfl⟩
    rw [wordOnes_word_sturmianCoding α θ hα0 hα1 le_rfl]
    have h1 : a ≤ ⌊(b : ℝ) * α⌋ := Int.le_floor.mpr h.le
    have h2 : ⌊(b : ℝ) * α⌋ ≤ ⌊θ + (b : ℝ) * α⌋ - ⌊θ⌋ := by
      have e : θ + (b : ℝ) * α = (⌊θ⌋ : ℝ) + (Int.fract θ + (b : ℝ) * α) := by
        linarith [Int.floor_add_fract θ]
      rw [e, Int.floor_intCast_add, add_sub_cancel_left]
      exact Int.floor_mono (by linarith [Int.fract_nonneg θ])
    exact h1.trans h2
  · intro h
    have hw := h (WordGraph.word (sturmianCoding α 0) 0 b) ⟨0, rfl⟩
    rw [wordOnes_word_sturmianCoding α 0 hα0 hα1 le_rfl] at hw
    simp only [zero_add, Int.floor_zero, sub_zero] at hw
    have hle : (a : ℝ) ≤ (b : ℝ) * α := Int.le_floor.mp hw
    have hirr : Irrational ((b : ℝ) * α) := by
      have := hα.intCast_mul (m := (b : ℤ)) (by exact_mod_cast hb.ne')
      simpa using this
    exact lt_of_le_of_ne hle fun h' => hirr.ne_int a h'.symm

#audit_axioms wordOnes_succ
#audit_axioms wordOnes_word_sturmianCoding
#audit_axioms mem_language_sturmianSubshift_iff_compare
#audit_axioms intCast_lt_mul_iff_forall_mem_language

end SimpleKazhdanSofic
end GroupApproximation
