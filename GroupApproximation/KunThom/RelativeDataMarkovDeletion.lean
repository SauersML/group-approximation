import GroupApproximation.Sofic.Asymptotics
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Markov deletion at a vanishing threshold

The relative cluster functor of Kun and Thom's Lemma 4.3 needs errors at most a
vanishing threshold `τ n` times the scale of every matched object, while the matching
estimates bound only total errors.  Markov's inequality closes the gap.  If every weight
is at most `c` times its scale, the objects whose error exceeds `τ n` times their scale
weigh at most `c / τ n` times the total error.  The deleted weight is negligible once the
normalized total error is `o(τ n)`.

* `sum_ite_le_div_mul_sum`: the finite inequality.
* `negligible_badWeight_of_threshold`: the asymptotic form.
* `ite_and_le_add` and `negligible_badWeight_and`: two deletion conditions at once.
* `sum_filter_not_eq_sum_ite`: the deleted weight as a sum over the `Finset` of bad
  objects.
* `negligible_compl_started_filter`: a matching domain restricted to good objects from a
  start index on, and empty before, misses only the weight outside the domain and the
  deleted weight.
-/

namespace GroupApproximation
namespace RelativeDataMarkov

open scoped BigOperators

/-- **Markov's inequality at a threshold.** -/
theorem sum_ite_le_div_mul_sum {ι : Type*} [Fintype ι] (w s e : ι → ℝ)
    (he : ∀ i, 0 ≤ e i) {c τ : ℝ} (hc : 0 ≤ c) (hτ : 0 < τ) (hws : ∀ i, w i ≤ c * s i) :
    (∑ i, if e i ≤ τ * s i then 0 else w i) ≤ c / τ * ∑ i, e i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hcτ : 0 ≤ c / τ := div_nonneg hc hτ.le
  by_cases h : e i ≤ τ * s i
  · rw [if_pos h]
    exact mul_nonneg hcτ (he i)
  · rw [if_neg h]
    have hlt : τ * s i < e i := not_le.mp h
    have h1 : c * (τ * s i) ≤ c * e i := mul_le_mul_of_nonneg_left hlt.le hc
    have h3 : w i * τ ≤ c * s i * τ := mul_le_mul_of_nonneg_right (hws i) hτ.le
    have h2 : c / τ * e i = c * e i / τ := by ring
    rw [h2, le_div_iff₀ hτ]
    linarith

/-- **Deleted weight at a vanishing threshold.** -/
theorem negligible_badWeight_of_threshold {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    {N : ℕ → ℝ} (hN : ∀ n, 0 ≤ N n) (w s e : ∀ n, ι n → ℝ) (hw : ∀ n i, 0 ≤ w n i)
    (he : ∀ n i, 0 ≤ e n i) {c : ℝ} (hc : 0 ≤ c) (hws : ∀ n i, w n i ≤ c * s n i)
    (τ : ℕ → ℝ) (hτ : ∀ n, 0 < τ n)
    (hdensity : Vanishing fun n ↦ (∑ i, e n i) / N n / τ n) :
    Negligible N fun n ↦ ∑ i, if e n i ≤ τ n * s n i then 0 else w n i := by
  show Vanishing fun n ↦ (∑ i, if e n i ≤ τ n * s n i then 0 else w n i) / N n
  refine Vanishing.squeeze (fun n ↦ ?_) (fun n ↦ ?_) (Vanishing.const_mul c hdensity)
  · apply div_nonneg _ (hN n)
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact le_rfl
    · exact hw n i
  · have hfin := sum_ite_le_div_mul_sum (w n) (s n) (e n) (he n) hc (hτ n) (hws n)
    calc (∑ i, if e n i ≤ τ n * s n i then 0 else w n i) / N n
        ≤ (c / τ n * ∑ i, e n i) / N n := div_le_div_of_nonneg_right hfin (hN n)
      _ = c * ((∑ i, e n i) / N n / τ n) := by ring

/-- Two deletion conditions cost at most the sum of their deleted weights. -/
theorem ite_and_le_add (P Q : Prop) [Decidable P] [Decidable Q] {w : ℝ} (hw : 0 ≤ w) :
    (if P ∧ Q then 0 else w) ≤ (if P then 0 else w) + (if Q then 0 else w) := by
  have hP0 : 0 ≤ (if P then (0 : ℝ) else w) := by split_ifs <;> linarith
  have hQ0 : 0 ≤ (if Q then (0 : ℝ) else w) := by split_ifs <;> linarith
  by_cases hPQ : P ∧ Q
  · rw [if_pos hPQ]
    linarith
  · rw [if_neg hPQ]
    by_cases hP : P
    · have hQ : ¬ Q := fun hQ ↦ hPQ ⟨hP, hQ⟩
      rw [if_neg hQ]
      linarith
    · rw [if_neg hP]
      linarith

theorem negligible_badWeight_and {ι : ℕ → Type*} [∀ n, Fintype (ι n)] {N : ℕ → ℝ}
    (hN : ∀ n, 0 ≤ N n) (w : ∀ n, ι n → ℝ) (hw : ∀ n i, 0 ≤ w n i)
    (P Q : ∀ n, ι n → Prop) [∀ n, DecidablePred (P n)] [∀ n, DecidablePred (Q n)]
    (hP : Negligible N fun n ↦ ∑ i, if P n i then 0 else w n i)
    (hQ : Negligible N fun n ↦ ∑ i, if Q n i then 0 else w n i) :
    Negligible N fun n ↦ ∑ i, if P n i ∧ Q n i then 0 else w n i := by
  refine Negligible.mono_nonneg hN (fun n ↦ ?_) (fun n ↦ ?_) (hP.add hQ)
  · apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact le_rfl
    · exact hw n i
  · show (∑ i, if P n i ∧ Q n i then 0 else w n i) ≤
      (∑ i, if P n i then 0 else w n i) + ∑ i, if Q n i then 0 else w n i
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ ↦ ite_and_le_add (P n i) (Q n i) (hw n i)

/-- The deleted weight is the weight of the `Finset` of bad objects. -/
theorem sum_filter_not_eq_sum_ite {ι : Type*} [Fintype ι] (p : ι → Prop)
    [DecidablePred p] (w : ι → ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ p i), w i = ∑ i, if p i then 0 else w i := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hp : p i
  · rw [if_neg (not_not.mpr hp), if_pos hp]
  · rw [if_pos hp, if_neg hp]

/-- **Started matching domains.**  A domain restricted to good objects from a start index
on, and empty before, misses the weight outside the domain and the bad weight. -/
theorem negligible_compl_started_filter {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    [∀ n, DecidableEq (ι n)] {N : ℕ → ℝ} (hN : ∀ n, 0 ≤ N n) (w : ∀ n, ι n → ℝ)
    (hw : ∀ n i, 0 ≤ w n i) (Dom : ∀ n, Finset (ι n)) (good : ∀ n, ι n → Prop)
    [∀ n, DecidablePred (good n)] (start : ℕ)
    (hDom : Negligible N fun n ↦ ∑ i ∈ Finset.univ \ Dom n, w n i)
    (hbad : Negligible N fun n ↦ ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ good n i), w n i) :
    Negligible N fun n ↦
      ∑ i ∈ Finset.univ \ (if start ≤ n then (Dom n).filter (good n) else ∅), w n i := by
  refine Vanishing.squeeze_eventually (hDom.add hbad) start fun n hn ↦ ⟨?_, ?_⟩
  · exact div_nonneg (Finset.sum_nonneg fun i _ ↦ hw n i) (hN n)
  · apply div_le_div_of_nonneg_right _ (hN n)
    show (∑ i ∈ Finset.univ \ (if start ≤ n then (Dom n).filter (good n) else ∅), w n i) ≤
      (∑ i ∈ Finset.univ \ Dom n, w n i) +
        ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ good n i), w n i
    rw [if_pos hn]
    have hsub : Finset.univ \ (Dom n).filter (good n) ⊆
        (Finset.univ \ Dom n) ∪ Finset.univ.filter (fun i ↦ ¬ good n i) := by
      intro i hi
      rw [Finset.mem_sdiff, Finset.mem_filter] at hi
      rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter]
      by_cases hD : i ∈ Dom n
      · exact Or.inr ⟨Finset.mem_univ i, fun hg ↦ hi.2 ⟨hD, hg⟩⟩
      · exact Or.inl ⟨Finset.mem_univ i, hD⟩
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ ↦ hw n i
    have hui := Finset.sum_union_inter (s₁ := Finset.univ \ Dom n)
      (s₂ := Finset.univ.filter (fun i ↦ ¬ good n i)) (f := w n)
    have hinter : 0 ≤ ∑ i ∈ (Finset.univ \ Dom n) ∩ Finset.univ.filter (fun i ↦ ¬ good n i),
        w n i :=
      Finset.sum_nonneg fun i _ ↦ hw n i
    linarith

end RelativeDataMarkov
end GroupApproximation
