import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Algo
import Mathlib.Tactic.LinearCombination

/-!
# Correctness of the parametric pseudo-remainder

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof step "Fixed-dimensional
feasibility is decidable over the real closed field".  Suppose the leading
coefficient `bl` of `B = b ++ [bl]` does not vanish at `ρ`.  Then the loop
`premLoop bl b t v` computes a remainder `r` of degree `< deg B` such that
`c · A = S · B + R` for some real `c > 0`, where `A` and `R` are the polynomials
of `v` and `r` (`premLoop_spec`).  The multipliers are squares `bl²`, so `c`
is positive.
-/

namespace GroupApproximation.Full.NN11b

open Polynomial

/-! ## Lengths -/

theorem length_upSmul (c : MvP) : ∀ u : List MvP, (upSmul c u).length = u.length
  | [] => rfl
  | a :: u => by
      show (upSmul c u).length + 1 = u.length + 1
      rw [length_upSmul c u]

theorem length_upAdd_le : ∀ (u v : List MvP) (n : ℕ), u.length ≤ n → v.length ≤ n →
    (upAdd u v).length ≤ n
  | [], _, _, _, hv => hv
  | _ :: _, [], _, hu, _ => hu
  | _ :: u, _ :: v, n, hu, hv => by
      have hu' : u.length + 1 ≤ n := hu
      have hv' : v.length + 1 ≤ n := hv
      have ih := length_upAdd_le u v (n - 1) (by omega) (by omega)
      show (upAdd u v).length + 1 ≤ n
      omega

theorem length_premStep_le (bl : MvP) (b : List MvP) (an : MvP) (a : List MvP)
    (h : b.length ≤ a.length) : (premStep bl b an a).length ≤ a.length := by
  unfold premStep
  exact length_upAdd_le _ _ _ (le_of_eq (length_upSmul _ a))
    (by rw [length_upSmul, List.length_append, List.length_replicate]; omega)

/-! ## The polynomial of one reduction step -/

theorem toPoly_replicate_append (ρ : ℕ → ℝ) : ∀ (m : ℕ) (b : List MvP),
    toPoly ρ (List.replicate m [] ++ b) = X ^ m * toPoly ρ b
  | 0, b => by
      show toPoly ρ b = X ^ 0 * toPoly ρ b
      rw [pow_zero, one_mul]
  | m + 1, b => by
      show C (mvEval ρ []) + X * toPoly ρ (List.replicate m [] ++ b) = X ^ (m + 1) * toPoly ρ b
      rw [toPoly_replicate_append ρ m b, mvEval_nil, C_0, zero_add]
      ring

theorem toPoly_premStep (ρ : ℕ → ℝ) (bl : MvP) (b : List MvP) (an : MvP) (a : List MvP) :
    toPoly ρ (premStep bl b an a) =
      C (mvEval ρ bl) * C (mvEval ρ bl) * toPoly ρ a -
        C (mvEval ρ bl) * C (mvEval ρ an) * (X ^ (a.length - b.length) * toPoly ρ b) := by
  unfold premStep
  simp only [toPoly_upAdd, toPoly_upSmul, toPoly_replicate_append, mvEval_mul, mvEval_neg,
    C_mul, C_neg]
  ring

theorem degree_toPoly_lt (ρ : ℕ → ℝ) (u : List MvP) :
    (toPoly ρ u).degree < (u.length : WithBot ℕ) := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_toPoly, getD_of_length_le [] u m hm, mvEval_nil]

/-! ## The loop -/

/-- The pseudo-remainder specification: `r` (top coefficient first) is shorter than
`b ++ [bl]`, and `c · A = S · B + R` with `c > 0`. -/
structure PRemOK (ρ : ℕ → ℝ) (bl : MvP) (b v r : List MvP) : Prop where
  len : r.length ≤ b.length
  eqn : ∃ c : ℝ, 0 < c ∧ ∃ S : ℝ[X],
    C c * toPoly ρ v.reverse = S * toPoly ρ (b ++ [bl]) + toPoly ρ r.reverse

theorem pRemOK_self (ρ : ℕ → ℝ) (bl : MvP) (b v : List MvP) (h : v.length ≤ b.length) :
    PRemOK ρ bl b v v :=
  ⟨h, ⟨1, one_pos, ⟨0, by rw [C_1, one_mul, zero_mul, zero_add]⟩⟩⟩

/-- **Pseudo-remainder**: with `bl` not vanishing at `ρ`, `premLoop` returns a
remainder of degree `< deg B`. -/
theorem premLoop_spec (ρ : ℕ → ℝ) (bl : MvP) (b : List MvP) (hbl : mvEval ρ bl ≠ 0) :
    ∀ (t : ℕ) (v : List MvP), v.length ≤ t + b.length → PRemOK ρ bl b v (premLoop bl b t v)
  | 0, v, hv => by
      show PRemOK ρ bl b v v
      exact pRemOK_self ρ bl b v (by omega)
  | t + 1, [], _ => by
      show PRemOK ρ bl b [] []
      exact pRemOK_self ρ bl b [] (Nat.zero_le _)
  | t + 1, an :: w, hv => by
      by_cases hw : w.length < b.length
      · have e : premLoop bl b (t + 1) (an :: w) = an :: w := by
          rw [premLoop, if_pos hw]
        rw [e]
        exact pRemOK_self ρ bl b (an :: w) (by rw [List.length_cons]; omega)
      · have hk : b.length ≤ w.length := Nat.le_of_not_lt hw
        have e : premLoop bl b (t + 1) (an :: w) =
            premLoop bl b t (premStep bl b an w.reverse).reverse := by
          rw [premLoop, if_neg hw]
        rw [e]
        have hlen : (premStep bl b an w.reverse).reverse.length ≤ t + b.length := by
          rw [List.length_reverse]
          have h1 := length_premStep_le bl b an w.reverse (by rw [List.length_reverse]; exact hk)
          rw [List.length_reverse] at h1
          have h2 : w.length + 1 ≤ t + 1 + b.length := by
            rw [List.length_cons] at hv
            exact hv
          omega
        obtain ⟨hr, c', hc', S', hS'⟩ := premLoop_spec ρ bl b hbl t _ hlen
        rw [List.reverse_reverse, toPoly_premStep, List.length_reverse] at hS'
        refine ⟨hr, ⟨c' * (mvEval ρ bl * mvEval ρ bl), mul_pos hc' (mul_self_pos.2 hbl),
          ⟨S' + C c' * C (mvEval ρ bl) * C (mvEval ρ an) * X ^ (w.length - b.length), ?_⟩⟩⟩
        have hB := toPoly_append_single ρ bl b
        have hX : (X : ℝ[X]) ^ (w.length - b.length) * X ^ b.length = X ^ w.length := by
          rw [← pow_add, Nat.sub_add_cancel hk]
        rw [List.reverse_cons, toPoly_append_single ρ an w.reverse, List.length_reverse, C_mul,
          C_mul]
        linear_combination hS' -
          C c' * C (mvEval ρ bl) * C (mvEval ρ an) * X ^ (w.length - b.length) * hB -
          C c' * C (mvEval ρ bl) * C (mvEval ρ an) * C (mvEval ρ bl) * hX

end GroupApproximation.Full.NN11b
