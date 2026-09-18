import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Taq
import Mathlib.Tactic.LinearCombination

/-!
# The Ben-Or--Kozen--Reif identity

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof step "Fixed-dimensional
feasibility is decidable over the real closed field".  For polynomials `q_1, …, q_m`
and a sign vector `σ ∈ {-1, 0, 1}^m`,

  `bkrSum P qs σ = 2^m · #{x ∈ ℝ : P(x) = 0, sgn q_j(x) = σ_j for all j}`

(`bkrSum_eq`).  So `0 < bkrSum P qs σ` exactly when some root of `P` realizes `σ`
(`bkrSum_pos_iff`).  The proof goes pointwise: at every real `x`, the weighted sum
`∑_e w(σ, e) · sgn(∏ q_j^{e_j})(x)` factors coordinatewise into the `3 × 3`
identities `∑_{k ≤ 2} w(s, k) t^k = 2·[t = s]` (`weight1_sum`).
-/

namespace GroupApproximation.Full.NN11b

open Polynomial

/-! ## Signs -/

theorem sgn_mem3 (a : ℝ) : sgn a = 0 ∨ sgn a = 1 ∨ sgn a = -1 := by
  by_cases h : a = 0
  · exact Or.inl (by rw [h, ST.sgn_zero])
  · exact Or.inr (ST.sgn_cases h)

/-- The Ben-Or--Kozen--Reif matrix identity, one coordinate at a time. -/
theorem weight1_sum (s t : ℤ) (hs : s = 0 ∨ s = 1 ∨ s = -1) (ht : t = 0 ∨ t = 1 ∨ t = -1) :
    weight1 s 0 * t ^ 0 + weight1 s 1 * t ^ 1 + weight1 s 2 * t ^ 2 =
      2 * (if t = s then 1 else 0) := by
  rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;> decide

/-! ## Reindexing sums over exponent vectors -/

theorem sum_flatMap3 (g : List ℕ → ℤ) : ∀ l : List (List ℕ),
    ((l.flatMap fun e => [0 :: e, 1 :: e, 2 :: e]).map g).sum =
      (l.map fun e => g (0 :: e) + g (1 :: e) + g (2 :: e)).sum
  | [] => rfl
  | e :: l => by
      simp only [List.flatMap_cons, List.map_append, List.sum_append_int, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, sum_flatMap3 g l]
      ring

theorem list_sum_finset_sum (s : Finset ℝ) (g : List ℕ → ℝ → ℤ) : ∀ l : List (List ℕ),
    (l.map fun e => ∑ x ∈ s, g e x).sum = ∑ x ∈ s, (l.map fun e => g e x).sum
  | [] => by
      rw [List.map_nil, List.sum_nil, eq_comm]
      exact Finset.sum_eq_zero fun _ _ => rfl
  | e :: l => by
      rw [List.map_cons, List.sum_cons, list_sum_finset_sum s g l, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [List.map_cons, List.sum_cons]

/-! ## The pointwise identity -/

/-- **Pointwise Ben-Or--Kozen--Reif identity**: at every real `x`, the weighted sum of
the signs of the products `∏ q_j^{e_j}` is `2^m` times the indicator of `sgnVec qs x = σ`. -/
theorem bkr_point (x : ℝ) : ∀ (qs : List ℝ[X]) (σ : List ℤ), σ.length = qs.length →
    (∀ s ∈ σ, s = 0 ∨ s = 1 ∨ s = -1) →
    ((expVecs qs.length).map fun e => weight σ e * sgn ((prodPow qs e).eval x)).sum =
      2 ^ qs.length * (if sgnVec qs x = σ then 1 else 0)
  | [], [], _, _ => by
      have h1 : (prodPow [] []).eval x = 1 := eval_one
      have h2 : sgnVec [] x = [] := rfl
      have h3 : weight [] [] = 1 := rfl
      show weight [] [] * sgn ((prodPow [] []).eval x) + 0 =
        2 ^ 0 * (if sgnVec [] x = [] then 1 else 0)
      rw [if_pos h2, h1, h3, ST.sgn_of_pos one_pos]
      norm_num
  | [], _ :: _, h, _ => by
      rw [List.length_cons, List.length_nil] at h
      omega
  | _ :: _, [], h, _ => by
      rw [List.length_cons, List.length_nil] at h
      omega
  | q :: qs, s :: σ, h, hσ => by
      have hlen : σ.length = qs.length := by
        rw [List.length_cons, List.length_cons] at h
        omega
      have hs : s = 0 ∨ s = 1 ∨ s = -1 := hσ s (List.mem_cons.2 (Or.inl rfl))
      have hσ' : ∀ s' ∈ σ, s' = 0 ∨ s' = 1 ∨ s' = -1 :=
        fun s' hs' => hσ s' (List.mem_cons.2 (Or.inr hs'))
      have ih := bkr_point x qs σ hlen hσ'
      have hk : ∀ (k : ℕ) (e : List ℕ),
          weight (s :: σ) (k :: e) * sgn ((prodPow (q :: qs) (k :: e)).eval x) =
            weight1 s k * sgn (q.eval x) ^ k * (weight σ e * sgn ((prodPow qs e).eval x)) := by
        intro k e
        show weight1 s k * weight σ e * sgn ((q ^ k * prodPow qs e).eval x) = _
        rw [eval_mul, eval_pow, ST.sgn_mul, ST.sgn_pow]
        ring
      have key : ∀ e : List ℕ,
          weight (s :: σ) (0 :: e) * sgn ((prodPow (q :: qs) (0 :: e)).eval x) +
            weight (s :: σ) (1 :: e) * sgn ((prodPow (q :: qs) (1 :: e)).eval x) +
            weight (s :: σ) (2 :: e) * sgn ((prodPow (q :: qs) (2 :: e)).eval x) =
          2 * (if sgn (q.eval x) = s then 1 else 0) *
            (weight σ e * sgn ((prodPow qs e).eval x)) := by
        intro e
        rw [hk 0 e, hk 1 e, hk 2 e]
        linear_combination (weight σ e * sgn ((prodPow qs e).eval x)) *
          weight1_sum s (sgn (q.eval x)) hs (sgn_mem3 (q.eval x))
      show (((expVecs qs.length).flatMap fun e => [0 :: e, 1 :: e, 2 :: e]).map
          fun e => weight (s :: σ) e * sgn ((prodPow (q :: qs) e).eval x)).sum =
        2 ^ (qs.length + 1) * (if sgnVec (q :: qs) x = s :: σ then 1 else 0)
      rw [sum_flatMap3]
      simp only [key]
      rw [List.sum_map_mul_left, ih]
      by_cases h1 : sgn (q.eval x) = s
      · by_cases h2 : sgnVec qs x = σ
        · have h3 : sgnVec (q :: qs) x = s :: σ := by
            show sgn (q.eval x) :: sgnVec qs x = s :: σ
            rw [h1, h2]
          rw [if_pos h1, if_pos h2, if_pos h3]
          ring
        · have h3 : ¬ sgnVec (q :: qs) x = s :: σ := fun h3 => by
            have h3' : sgn (q.eval x) :: sgnVec qs x = s :: σ := h3
            exact h2 (List.cons.inj h3').2
          rw [if_pos h1, if_neg h2, if_neg h3]
          ring
      · have h3 : ¬ sgnVec (q :: qs) x = s :: σ := fun h3 => by
          have h3' : sgn (q.eval x) :: sgnVec qs x = s :: σ := h3
          exact h1 (List.cons.inj h3').1
        rw [if_neg h1, if_neg h3]
        ring

/-! ## Counting roots with a prescribed sign vector -/

/-- **Ben-Or--Kozen--Reif identity**: `bkrSum P qs σ = 2^m · #{x : P(x) = 0, sgnVec qs x = σ}`. -/
theorem bkrSum_eq (P : ℝ[X]) (qs : List ℝ[X]) (σ : List ℤ) (hlen : σ.length = qs.length)
    (hσ : ∀ s ∈ σ, s = 0 ∨ s = 1 ∨ s = -1) :
    bkrSum P qs σ =
      2 ^ qs.length * ∑ x ∈ P.roots.toFinset, (if sgnVec qs x = σ then (1 : ℤ) else 0) := by
  unfold bkrSum taq
  simp only [Finset.mul_sum]
  rw [list_sum_finset_sum]
  exact Finset.sum_congr rfl fun x _ => bkr_point x qs σ hlen hσ

/-- **Sign realization at roots**: `0 < bkrSum P qs σ` iff some root of `P` realizes `σ`. -/
theorem bkrSum_pos_iff (P : ℝ[X]) (qs : List ℝ[X]) (σ : List ℤ) (hlen : σ.length = qs.length)
    (hσ : ∀ s ∈ σ, s = 0 ∨ s = 1 ∨ s = -1) :
    0 < bkrSum P qs σ ↔ ∃ x ∈ P.roots, sgnVec qs x = σ := by
  rw [bkrSum_eq P qs σ hlen hσ]
  constructor
  · intro h
    by_contra hne
    have h0 : ∑ x ∈ P.roots.toFinset, (if sgnVec qs x = σ then (1 : ℤ) else 0) = 0 :=
      Finset.sum_eq_zero fun x hx => by
        have hx' : ¬ sgnVec qs x = σ := fun hx' => hne ⟨x, Multiset.mem_toFinset.1 hx, hx'⟩
        exact if_neg hx'
    rw [h0, mul_zero] at h
    exact lt_irrefl 0 h
  · rintro ⟨x, hx, hx'⟩
    have hnn : ∀ y ∈ P.roots.toFinset, (0 : ℤ) ≤ if sgnVec qs y = σ then 1 else 0 := by
      intro y _
      by_cases hy : sgnVec qs y = σ
      · rw [if_pos hy]
        exact zero_le_one
      · exact le_of_eq (if_neg hy).symm
    have h2 := Finset.single_le_sum hnn (Multiset.mem_toFinset.2 hx)
    rw [if_pos hx'] at h2
    exact mul_pos (pow_pos zero_lt_two _) (lt_of_lt_of_le zero_lt_one h2)

end GroupApproximation.Full.NN11b
