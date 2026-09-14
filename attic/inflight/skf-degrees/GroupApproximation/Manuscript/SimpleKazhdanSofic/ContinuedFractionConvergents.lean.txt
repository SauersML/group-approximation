import GroupApproximation.Manuscript.SimpleKazhdanSofic.ContinuedFractionExpansion
import GroupApproximation.Meta.AxiomGuard

/-!
# Each digit of `[0; a_0, a_1, …]` is one strict comparison with a rational

`simple_kazhdan_sofic_group.tex` (origin tip 696c4b602), proof of `cor:wp`, second paragraph:
"each digit is decided by one strict comparison with a rational computed from earlier digits".

For digits `a_k ∈ {1, 2}` and the tails `y_k` of `ContinuedFractionExpansion`:
* `conv a k = (p_{k-1}, p_k, q_{k-1}, q_k)` collects the last two convergents of `[0; a_0, …, a_{k-1}]`;
* `tail_zero_eq`: `y_0 = (p_k + p_{k-1} y_k) / (q_k + q_{k-1} y_k)`;
* `det_conv`: `p_{k-1} q_k - p_k q_{k-1} = (-1)^k`;
* `digit_eq_of_answer`: with `A = 2p_k + p_{k-1}` and `B = 2q_k + q_{k-1}`, the digit `a_k` is `2`
  exactly when `k % 2` equals the answer `[A < B y_0]`. Indeed `a_k = 2` exactly when `y_k < 1/2`,
  and `A - B y_0` has the sign of `(-1)^k (1 - 2 y_k)` over a positive denominator.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace ContinuedFractionExpansion

/-- `conv a k = (p_{k-1}, p_k, q_{k-1}, q_k)` for `[0; a_0, …, a_{k-1}]`. -/
def conv (a : ℕ → ℕ) : ℕ → ℕ × ℕ × ℕ × ℕ
  | 0 => (1, 0, 0, 1)
  | k + 1 => ((conv a k).2.1, a k * (conv a k).2.1 + (conv a k).1,
      (conv a k).2.2.2, a k * (conv a k).2.2.2 + (conv a k).2.2.1)

theorem conv_succ (a : ℕ → ℕ) (k : ℕ) :
    conv a (k + 1) = ((conv a k).2.1, a k * (conv a k).2.1 + (conv a k).1,
      (conv a k).2.2.2, a k * (conv a k).2.2.2 + (conv a k).2.2.1) :=
  rfl

variable {a : ℕ → ℕ}

theorem one_le_conv_q (ha : ∀ k, a k = 1 ∨ a k = 2) : ∀ k, 1 ≤ (conv a k).2.2.2
  | 0 => le_rfl
  | k + 1 => by
    rw [conv_succ]
    have h := one_le_conv_q ha k
    have hk : 1 ≤ a k := by rcases ha k with h' | h' <;> omega
    exact le_add_right (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))

/-- `p_{k-1} q_k - p_k q_{k-1} = (-1)^k`. -/
theorem det_conv (a : ℕ → ℕ) :
    ∀ k, ((conv a k).1 : ℤ) * (conv a k).2.2.2 - (conv a k).2.1 * (conv a k).2.2.1 = (-1) ^ k
  | 0 => by simp [conv]
  | k + 1 => by
    rw [conv_succ, pow_succ, ← det_conv a k]
    push_cast
    ring

/-- `y_0 = (p_k + p_{k-1} y_k) / (q_k + q_{k-1} y_k)`. -/
theorem tail_zero_eq (ha : ∀ k, a k = 1 ∨ a k = 2) :
    ∀ k, tail a ha 0 = ((conv a k).2.1 + (conv a k).1 * tail a ha k) /
      ((conv a k).2.2.2 + (conv a k).2.2.1 * tail a ha k)
  | 0 => by simp [conv]
  | k + 1 => by
    rw [tail_zero_eq ha k, tail_eq ha k, conv_succ]
    push_cast
    have ht := (tail_mem ha (k + 1)).1
    have hq : (1 : ℝ) ≤ (conv a k).2.2.2 := by exact_mod_cast one_le_conv_q ha k
    have hq' : (0 : ℝ) ≤ (conv a k).2.2.1 := Nat.cast_nonneg _
    have hak : (0 : ℝ) ≤ a k := Nat.cast_nonneg _
    have hu : (0 : ℝ) < a k + tail a ha (k + 1) := by linarith
    have hden : (0 : ℝ) < (conv a k).2.2.2 * (a k + tail a ha (k + 1)) + (conv a k).2.2.1 := by
      nlinarith
    have hden' : (0 : ℝ) < a k * (conv a k).2.2.2 + (conv a k).2.2.1 +
        (conv a k).2.2.2 * tail a ha (k + 1) := by nlinarith
    field_simp
    ring

theorem digit_eq_two_iff (ha : ∀ k, a k = 1 ∨ a k = 2) (k : ℕ) : a k = 2 ↔ tail a ha k < 1 / 2 := by
  have ht1 := (tail_mem ha (k + 1)).1
  have ht2 := (tail_mem ha (k + 1)).2
  have hak : (0 : ℝ) ≤ a k := Nat.cast_nonneg _
  have hpos : (0 : ℝ) < a k + tail a ha (k + 1) := by linarith
  rw [tail_eq ha k, ← one_div, div_lt_iff₀ hpos]
  rcases ha k with h | h
  · rw [h]
    constructor
    · intro h'
      exact absurd h' (by decide)
    · intro h'
      exact absurd h' (not_lt.2 (by push_cast; linarith))
  · rw [h]
    constructor
    · intro _
      push_cast
      linarith
    · intro _
      rfl

theorem tail_ne_half (ha : ∀ k, a k = 1 ∨ a k = 2) (k : ℕ) : tail a ha k ≠ 1 / 2 := by
  intro h
  exact irrational_tail ha k ⟨1 / 2, by rw [h]; norm_num⟩

/-- `A < B y_0` exactly when `k` is even and `y_k > 1/2`, or `k` is odd and `y_k < 1/2`, where
`A = 2p_k + p_{k-1}` and `B = 2q_k + q_{k-1}`. -/
theorem lt_mul_tail_zero_iff (ha : ∀ k, a k = 1 ∨ a k = 2) (k : ℕ) :
    ((2 * (conv a k).2.1 + (conv a k).1 : ℕ) : ℝ) <
        ((2 * (conv a k).2.2.2 + (conv a k).2.2.1 : ℕ) : ℝ) * tail a ha 0 ↔
      (k % 2 = 0 ↔ 1 / 2 < tail a ha k) := by
  rw [tail_zero_eq ha k]
  push_cast
  have ht := (tail_mem ha k).1
  have hq : (1 : ℝ) ≤ (conv a k).2.2.2 := by exact_mod_cast one_le_conv_q ha k
  have hq' : (0 : ℝ) ≤ (conv a k).2.2.1 := Nat.cast_nonneg _
  have hden : (0 : ℝ) < (conv a k).2.2.2 + (conv a k).2.2.1 * tail a ha k := by nlinarith
  rw [mul_div_assoc', lt_div_iff₀ hden]
  have hdet : ((conv a k).1 : ℝ) * (conv a k).2.2.2 - (conv a k).2.1 * (conv a k).2.2.1 =
      (-1) ^ k := by exact_mod_cast det_conv a k
  have key : (2 * ((conv a k).2.1 : ℝ) + (conv a k).1) *
        ((conv a k).2.2.2 + (conv a k).2.2.1 * tail a ha k) -
      (2 * ((conv a k).2.2.2 : ℝ) + (conv a k).2.2.1) *
        ((conv a k).2.1 + (conv a k).1 * tail a ha k) =
      (((conv a k).1 : ℝ) * (conv a k).2.2.2 - (conv a k).2.1 * (conv a k).2.2.1) *
        (1 - 2 * tail a ha k) := by ring
  rw [hdet] at key
  have hne := tail_ne_half ha k
  rcases Nat.even_or_odd k with he | ho
  · rw [he.neg_one_pow, one_mul] at key
    have hk : k % 2 = 0 := Nat.even_iff.1 he
    simp only [hk, true_iff]
    constructor
    · intro h; linarith
    · intro h; linarith
  · rw [ho.neg_one_pow] at key
    have hk : k % 2 = 1 := Nat.odd_iff.1 ho
    simp only [hk, (by decide : ¬ ((1 : ℕ) = 0)), false_iff, not_lt]
    constructor
    · intro h; linarith
    · intro h
      have h' : tail a ha k < 1 / 2 := lt_of_le_of_ne h hne
      linarith

open Classical in
/-- **The digit from one comparison.**  `a_k = 2` exactly when `k % 2` equals the answer
`[A < B y_0]`, with `A = 2p_k + p_{k-1}` and `B = 2q_k + q_{k-1}`. -/
theorem digit_eq_of_answer (ha : ∀ k, a k = 1 ∨ a k = 2) (k : ℕ) :
    a k = if k % 2 = (if ((2 * (conv a k).2.1 + (conv a k).1 : ℕ) : ℝ) <
        ((2 * (conv a k).2.2.2 + (conv a k).2.2.1 : ℕ) : ℝ) * tail a ha 0 then 1 else 0)
      then 2 else 1 := by
  have hcmp := lt_mul_tail_zero_iff ha k
  have hne := tail_ne_half ha k
  have hone : 1 / 2 < tail a ha k → a k = 1 := fun h => by
    rcases ha k with h' | h'
    · exact h'
    · exact absurd ((digit_eq_two_iff ha k).1 h') (not_lt.2 h.le)
  have htwo : ¬ 1 / 2 < tail a ha k → a k = 2 := fun h =>
    (digit_eq_two_iff ha k).2 (lt_of_le_of_ne (not_lt.1 h) hne)
  rcases Nat.mod_two_eq_zero_or_one k with h0 | h0
  · by_cases hq : ((2 * (conv a k).2.1 + (conv a k).1 : ℕ) : ℝ) <
        ((2 * (conv a k).2.2.2 + (conv a k).2.2.1 : ℕ) : ℝ) * tail a ha 0
    · rw [if_pos hq, if_neg (by omega)]
      exact hone ((hcmp.1 hq).1 h0)
    · rw [if_neg hq, if_pos h0]
      exact htwo fun h => hq (hcmp.2 ⟨fun _ => h, fun _ => h0⟩)
  · by_cases hq : ((2 * (conv a k).2.1 + (conv a k).1 : ℕ) : ℝ) <
        ((2 * (conv a k).2.2.2 + (conv a k).2.2.1 : ℕ) : ℝ) * tail a ha 0
    · rw [if_pos hq, if_pos h0]
      exact htwo fun h => absurd ((hcmp.1 hq).2 h) (by omega)
    · rw [if_neg hq, if_neg (by omega)]
      exact hone (Classical.byContradiction fun h =>
        hq (hcmp.2 ⟨fun h0' => absurd h0' (by omega), fun h' => absurd h' h⟩))

#audit_axioms tail_zero_eq
#audit_axioms digit_eq_of_answer

end ContinuedFractionExpansion
end SimpleKazhdanSofic
end GroupApproximation
