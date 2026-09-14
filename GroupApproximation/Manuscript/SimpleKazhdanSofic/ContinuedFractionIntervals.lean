import GroupApproximation.Manuscript.SimpleKazhdanSofic.ContinuedFractionConvergents
import GroupApproximation.Meta.AxiomGuard

/-!
# The nested intervals of `[0; a_0, a_1, …]` for digits in `{1, 2}`

`simple_kazhdan_sofic_group.tex` (origin tip 696c4b602), proof of `cor:wp`, second paragraph (census
`7badee43dd9d`): "Every $S\subseteq\mathbb N$ has the degree of $[0;1+\chi_S(0),1+\chi_S(1),\dots]$".
These estimates are the ones through which `S` computes `α = y_0`:
* since `y_n ∈ (1/3, 3/4)`, `α` lies strictly between the rationals
  `endA = (3p_n + p_{n-1}) / (3q_n + q_{n-1})` and `endB = (4p_n + 3p_{n-1}) / (4q_n + 3q_{n-1})`
  (`sub_endA_mul_sub_endB_neg`);
* `2q_n ≥ n + 1` (`conv_q_growth`), so `|endA - endB| < 1/(n + 1)` (`abs_endA_sub_endB_lt`);
* for `c/e ≠ α`, some level puts `c/e` strictly on one side of both endpoints (`exists_sep`).
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace ContinuedFractionOracle

open ContinuedFractionExpansion

/-! ### Real estimates for the Möbius endpoints -/

theorem mobius_sign {P P' Q Q' y D : ℝ} (hD : P' * Q - P * Q' = D) (hD2 : D ^ 2 = 1)
    (hden : 0 < Q + Q' * y) (hdA : 0 < 3 * Q + Q') (hdB : 0 < 4 * Q + 3 * Q') (hy1 : 1 / 3 < y)
    (hy2 : y < 3 / 4) :
    ((P + P' * y) / (Q + Q' * y) - (3 * P + P') / (3 * Q + Q')) *
      ((P + P' * y) / (Q + Q' * y) - (4 * P + 3 * P') / (4 * Q + 3 * Q')) < 0 := by
  rw [div_sub_div _ _ hden.ne' hdA.ne', div_sub_div _ _ hden.ne' hdB.ne', div_mul_div_comm]
  refine div_neg_of_neg_of_pos ?_ (mul_pos (mul_pos hden hdA) (mul_pos hden hdB))
  have key : ((P + P' * y) * (3 * Q + Q') - (Q + Q' * y) * (3 * P + P')) *
      ((P + P' * y) * (4 * Q + 3 * Q') - (Q + Q' * y) * (4 * P + 3 * P')) =
        (P' * Q - P * Q') ^ 2 * ((3 * y - 1) * (4 * y - 3)) := by
    ring
  rw [key, hD, hD2, one_mul]
  exact mul_neg_of_pos_of_neg (by linarith) (by linarith)

theorem mobius_length {P P' Q Q' D : ℝ} (k : ℕ) (hD : P' * Q - P * Q' = D) (hD1 : |D| = 1)
    (hq : 1 ≤ Q) (hq' : 0 ≤ Q') (hgrow : (k : ℝ) + 1 ≤ 2 * Q) :
    |(3 * P + P') / (3 * Q + Q') - (4 * P + 3 * P') / (4 * Q + 3 * Q')| < 1 / ((k : ℝ) + 1) := by
  have hdA : 0 < 3 * Q + Q' := by linarith
  have hdB : 0 < 4 * Q + 3 * Q' := by linarith
  rw [div_sub_div _ _ hdA.ne' hdB.ne']
  have key : (3 * P + P') * (4 * Q + 3 * Q') - (3 * Q + Q') * (4 * P + 3 * P') =
      -5 * (P' * Q - P * Q') := by
    ring
  rw [key, hD, abs_div, abs_of_pos (mul_pos hdA hdB), abs_mul, hD1, mul_one,
    show |(-5 : ℝ)| = 5 by norm_num, div_lt_div_iff₀ (mul_pos hdA hdB) (by positivity)]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Q - 1) (by linarith : (0 : ℝ) ≤ Q),
    mul_nonneg (by linarith : (0 : ℝ) ≤ Q) hq', sq_nonneg Q']

/-- A point farther from `α` than the length of an interval around `α` lies on one side of it. -/
theorem sep_of_neg {x α E₁ E₂ : ℝ} (hprod : (α - E₁) * (α - E₂) < 0)
    (hlen : |E₁ - E₂| < |x - α|) : (x < E₁ ∧ x < E₂) ∨ (E₁ < x ∧ E₂ < x) := by
  rcases mul_neg_iff.1 hprod with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_neg (by linarith : E₁ - E₂ < 0)] at hlen
    rcases le_or_gt x α with hx | hx
    · rw [abs_of_nonpos (by linarith : x - α ≤ 0)] at hlen
      exact Or.inl ⟨by linarith, by linarith⟩
    · rw [abs_of_pos (by linarith : 0 < x - α)] at hlen
      exact Or.inr ⟨by linarith, by linarith⟩
  · rw [abs_of_pos (by linarith : 0 < E₁ - E₂)] at hlen
    rcases le_or_gt x α with hx | hx
    · rw [abs_of_nonpos (by linarith : x - α ≤ 0)] at hlen
      exact Or.inl ⟨by linarith, by linarith⟩
    · rw [abs_of_pos (by linarith : 0 < x - α)] at hlen
      exact Or.inr ⟨by linarith, by linarith⟩

theorem natCast_div_lt_iff {c e X Y : ℕ} (he : 0 < e) (hY : 0 < Y) :
    (c : ℝ) / e < (X : ℝ) / Y ↔ c * Y < X * e := by
  rw [div_lt_div_iff₀ (by exact_mod_cast he) (by exact_mod_cast hY)]
  norm_cast

theorem natCast_lt_div_iff {c e X Y : ℕ} (he : 0 < e) (hY : 0 < Y) :
    (X : ℝ) / Y < (c : ℝ) / e ↔ X * e < c * Y := by
  rw [div_lt_div_iff₀ (by exact_mod_cast hY) (by exact_mod_cast he)]
  norm_cast

theorem natCast_div_le_iff {c e X Y : ℕ} (he : 0 < e) (hY : 0 < Y) :
    (c : ℝ) / e ≤ (X : ℝ) / Y ↔ c * Y ≤ X * e := by
  rw [div_le_div_iff₀ (by exact_mod_cast he) (by exact_mod_cast hY)]
  norm_cast

theorem natCast_le_div_iff {c e X Y : ℕ} (he : 0 < e) (hY : 0 < Y) :
    (X : ℝ) / Y ≤ (c : ℝ) / e ↔ X * e ≤ c * Y := by
  rw [div_le_div_iff₀ (by exact_mod_cast hY) (by exact_mod_cast he)]
  norm_cast

/-! ### The interval of level `n` -/

variable {a : ℕ → ℕ}

theorem conv_q_growth (ha : ∀ k, a k = 1 ∨ a k = 2) :
    ∀ k, (conv a k).2.2.1 ≤ (conv a k).2.2.2 ∧ k + 1 ≤ (conv a k).2.2.2 + (conv a k).2.2.1
  | 0 => by
    show (0 : ℕ) ≤ 1 ∧ 0 + 1 ≤ 1 + 0
    omega
  | k + 1 => by
    obtain ⟨h1, h2⟩ := conv_q_growth ha k
    have hq := one_le_conv_q ha k
    have hk : 1 ≤ a k := by rcases ha k with h | h <;> omega
    show (conv a k).2.2.2 ≤ a k * (conv a k).2.2.2 + (conv a k).2.2.1 ∧
      k + 1 + 1 ≤ a k * (conv a k).2.2.2 + (conv a k).2.2.1 + (conv a k).2.2.2
    constructor <;> nlinarith

/-- `[0; a_0, …, a_{n-1} + 1/3] = (3p_n + p_{n-1}) / (3q_n + q_{n-1})`. -/
noncomputable def endA (a : ℕ → ℕ) (k : ℕ) : ℝ :=
  ((3 * (conv a k).2.1 + (conv a k).1 : ℕ) : ℝ) /
    ((3 * (conv a k).2.2.2 + (conv a k).2.2.1 : ℕ) : ℝ)

/-- `[0; a_0, …, a_{n-1} + 3/4] = (4p_n + 3p_{n-1}) / (4q_n + 3q_{n-1})`. -/
noncomputable def endB (a : ℕ → ℕ) (k : ℕ) : ℝ :=
  ((4 * (conv a k).2.1 + 3 * (conv a k).1 : ℕ) : ℝ) /
    ((4 * (conv a k).2.2.2 + 3 * (conv a k).2.2.1 : ℕ) : ℝ)

/-- `α` lies strictly between the two endpoints of every level. -/
theorem sub_endA_mul_sub_endB_neg (ha : ∀ k, a k = 1 ∨ a k = 2) (k : ℕ) :
    (tail a ha 0 - endA a k) * (tail a ha 0 - endB a k) < 0 := by
  have hq : (1 : ℝ) ≤ (conv a k).2.2.2 := by exact_mod_cast one_le_conv_q ha k
  have hq' : (0 : ℝ) ≤ (conv a k).2.2.1 := Nat.cast_nonneg _
  have hdet : ((conv a k).1 : ℝ) * (conv a k).2.2.2 - (conv a k).2.1 * (conv a k).2.2.1 =
      (-1) ^ k := by
    exact_mod_cast det_conv a k
  have hsq : ((-1 : ℝ) ^ k) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hne3 : tail a ha k ≠ 1 / 3 := fun h => irrational_tail ha k ⟨1 / 3, by rw [h]; norm_num⟩
  have hne4 : tail a ha k ≠ 3 / 4 := fun h => irrational_tail ha k ⟨3 / 4, by rw [h]; norm_num⟩
  have hy1 : 1 / 3 < tail a ha k := lt_of_le_of_ne (tail_mem ha k).1 (Ne.symm hne3)
  have hy2 : tail a ha k < 3 / 4 := lt_of_le_of_ne (tail_mem ha k).2 hne4
  have hden : (0 : ℝ) < (conv a k).2.2.2 + (conv a k).2.2.1 * tail a ha k := by nlinarith
  rw [endA, endB, tail_zero_eq ha k]
  push_cast
  exact mobius_sign hdet hsq hden (by linarith) (by linarith) hy1 hy2

/-- The interval of level `k` has length `< 1/(k + 1)`. -/
theorem abs_endA_sub_endB_lt (ha : ∀ k, a k = 1 ∨ a k = 2) (k : ℕ) :
    |endA a k - endB a k| < 1 / ((k : ℝ) + 1) := by
  obtain ⟨h1, h2⟩ := conv_q_growth ha k
  have hgrow : (k : ℝ) + 1 ≤ 2 * ((conv a k).2.2.2 : ℝ) := by
    exact_mod_cast (show k + 1 ≤ 2 * (conv a k).2.2.2 by omega)
  have hdet : ((conv a k).1 : ℝ) * (conv a k).2.2.2 - (conv a k).2.1 * (conv a k).2.2.1 =
      (-1) ^ k := by
    exact_mod_cast det_conv a k
  have hD1 : |((-1 : ℝ) ^ k)| = 1 := by
    rw [abs_pow, abs_neg, abs_one, one_pow]
  rw [endA, endB]
  push_cast
  exact mobius_length k hdet hD1 (by exact_mod_cast one_le_conv_q ha k) (Nat.cast_nonneg _) hgrow

/-- **A separating level exists** for every `c/e`, since `α` is irrational. -/
theorem exists_sep (ha : ∀ k, a k = 1 ∨ a k = 2) (c e : ℕ) :
    ∃ k, ((c : ℝ) / e < endA a k ∧ (c : ℝ) / e < endB a k) ∨
      (endA a k < (c : ℝ) / e ∧ endB a k < (c : ℝ) / e) := by
  have hne : (c : ℝ) / e ≠ tail a ha 0 := fun h =>
    irrational_tail ha 0 ⟨(c : ℚ) / e, by rw [← h]; norm_num⟩
  have hδ : 0 < |(c : ℝ) / e - tail a ha 0| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  exact ⟨k, sep_of_neg (sub_endA_mul_sub_endB_neg ha k) ((abs_endA_sub_endB_lt ha k).trans hk)⟩

end ContinuedFractionOracle
end SimpleKazhdanSofic
end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.ContinuedFractionOracle.sub_endA_mul_sub_endB_neg
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ContinuedFractionOracle.abs_endA_sub_endB_lt
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ContinuedFractionOracle.exists_sep
