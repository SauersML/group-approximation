import GroupApproximation.Matching.Selection
import Mathlib.Data.Countable.Defs

/-!
# Markov selection of good objects

At every index a finite family of objects carries nonnegative weights and a
countable family of nonnegative error counts, each with negligible total
against a fixed normalizing sequence.  Markov's inequality, applied to the
first `J n + 1` error levels at the diagonal level `J n` of
`Matching/Selection`, gives a predicate of good objects such that

* the total weight of the objects that are not good is negligible;
* every fixed error count is eventually at most any prescribed fraction of
  the weight, uniformly over the good objects.

This is the uniform form of the good-component step of the Kun--Thom
Theorem 4.1 blueprint (step G1f).
-/

namespace GroupApproximation
namespace CentralizerNormalizationUniform

open scoped BigOperators

/-- Markov's inequality: the weight of the objects whose error, scaled by
`c`, exceeds their weight is at most `c` times the total error. -/
theorem sum_ite_le_mul_sum {ι : Type*} [Fintype ι] (w e : ι → ℝ)
    (he : ∀ i, 0 ≤ e i) {c : ℝ} (hc : 0 ≤ c) :
    (∑ i, if c * e i ≤ w i then 0 else w i) ≤ c * ∑ i, e i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases h : c * e i ≤ w i
  · rw [if_pos h]
    exact mul_nonneg hc (he i)
  · rw [if_neg h]
    exact (not_le.mp h).le

/-- The objects whose first `J n + 1` error counts are at most their weight
divided by `J n + 1`. -/
def IsMarkovGood {ι : ℕ → Type*} (J : ℕ → ℕ) (w : ∀ n, ι n → ℝ)
    (e : ℕ → ∀ n, ι n → ℝ) (n : ℕ) (i : ι n) : Prop :=
  ∀ r ∈ Finset.range (J n + 1), ((J n : ℝ) + 1) * e r n i ≤ w n i

open Classical in
/-- Union bound over the first `J n + 1` error levels. -/
theorem ite_isMarkovGood_le_sum {ι : ℕ → Type*} (J : ℕ → ℕ) (w : ∀ n, ι n → ℝ)
    (e : ℕ → ∀ n, ι n → ℝ) (hw : ∀ n i, 0 ≤ w n i) (n : ℕ) (i : ι n) :
    (if IsMarkovGood J w e n i then 0 else w n i) ≤
      ∑ r ∈ Finset.range (J n + 1),
        (if ((J n : ℝ) + 1) * e r n i ≤ w n i then 0 else w n i) := by
  have hnonneg : ∀ r ∈ Finset.range (J n + 1),
      0 ≤ (if ((J n : ℝ) + 1) * e r n i ≤ w n i then 0 else w n i) := by
    intro r _
    split_ifs
    · exact le_rfl
    · exact hw n i
  by_cases hg : IsMarkovGood J w e n i
  · rw [if_pos hg]
    exact Finset.sum_nonneg hnonneg
  · rw [if_neg hg]
    have hex : ∃ r ∈ Finset.range (J n + 1),
        ¬ (((J n : ℝ) + 1) * e r n i ≤ w n i) := by
      by_contra hno
      push Not at hno
      exact hg hno
    obtain ⟨r, hr, hnot⟩ := hex
    calc w n i = (if ((J n : ℝ) + 1) * e r n i ≤ w n i then 0 else w n i) := by
          rw [if_neg hnot]
      _ ≤ ∑ r ∈ Finset.range (J n + 1),
            (if ((J n : ℝ) + 1) * e r n i ≤ w n i then 0 else w n i) :=
          Finset.single_le_sum hnonneg hr

/-- Accumulated normalized error up to level `k`, weighted by `k + 1`. -/
noncomputable def levelError {ι : ℕ → Type*} [∀ n, Fintype (ι n)] (N : ℕ → ℝ)
    (e : ℕ → ∀ n, ι n → ℝ) (n k : ℕ) : ℝ :=
  ((k : ℝ) + 1) * ∑ r ∈ Finset.range (k + 1), (∑ i, e r n i) / N n

open Classical in
/-- **Diagonal Markov selection** for error levels indexed by `ℕ`. -/
theorem exists_isGood_nat {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (N : ℕ → ℝ) (hN : ∀ n, 0 ≤ N n)
    (w : ∀ n, ι n → ℝ) (hw : ∀ n i, 0 ≤ w n i)
    (e : ℕ → ∀ n, ι n → ℝ) (he : ∀ r n i, 0 ≤ e r n i)
    (hneg : ∀ r, Negligible N fun n ↦ ∑ i, e r n i) :
    ∃ good : ∀ n, ι n → Prop,
      Negligible N (fun n ↦ ∑ i, if good n i then 0 else w n i) ∧
      ∀ (r : ℕ) (δ : ℝ), 0 < δ →
        ∃ M : ℕ, ∀ n ≥ M, ∀ i, good n i → e r n i ≤ δ * w n i := by
  have hE0 : ∀ n k, 0 ≤ levelError N e n k := by
    intro n k
    unfold levelError
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun r _ ↦
        div_nonneg (Finset.sum_nonneg fun i _ ↦ he r n i) (hN n))
  have hEvan : ∀ k, Vanishing fun n ↦ levelError N e n k := by
    intro k
    exact Vanishing.const_mul ((k : ℝ) + 1)
      (Vanishing.sum (Finset.range (k + 1)) (fun r n ↦ (∑ i, e r n i) / N n)
        fun r _ ↦ hneg r)
  obtain ⟨J, hJdiv, hJerr⟩ : ∃ J : ℕ → ℕ,
      (∀ k : ℕ, ∃ M : ℕ, ∀ n, M ≤ n → k ≤ J n) ∧
        Vanishing fun n ↦ levelError N e n (J n) :=
    ⟨diagonalLevel (levelError N e), diagonalLevel_diverges _ hEvan,
      diagonalLevel_error _ hE0 hEvan⟩
  refine ⟨IsMarkovGood J w e, ?_, ?_⟩
  · show Vanishing fun n ↦
      (∑ i, if IsMarkovGood J w e n i then 0 else w n i) / N n
    refine Vanishing.squeeze (fun n ↦ ?_) (fun n ↦ ?_) hJerr
    · apply div_nonneg _ (hN n)
      apply Finset.sum_nonneg
      intro i _
      split_ifs
      · exact le_rfl
      · exact hw n i
    · have hsum : (∑ i, if IsMarkovGood J w e n i then 0 else w n i) ≤
          ((J n : ℝ) + 1) * ∑ r ∈ Finset.range (J n + 1), ∑ i, e r n i := by
        calc (∑ i, if IsMarkovGood J w e n i then 0 else w n i)
            ≤ ∑ i, ∑ r ∈ Finset.range (J n + 1),
                (if ((J n : ℝ) + 1) * e r n i ≤ w n i then 0 else w n i) :=
              Finset.sum_le_sum fun i _ ↦ ite_isMarkovGood_le_sum J w e hw n i
          _ = ∑ r ∈ Finset.range (J n + 1), ∑ i,
                (if ((J n : ℝ) + 1) * e r n i ≤ w n i then 0 else w n i) :=
              Finset.sum_comm
          _ ≤ ∑ r ∈ Finset.range (J n + 1), ((J n : ℝ) + 1) * ∑ i, e r n i :=
              Finset.sum_le_sum fun r _ ↦
                sum_ite_le_mul_sum (w n) (e r n) (he r n) (by positivity)
          _ = ((J n : ℝ) + 1) * ∑ r ∈ Finset.range (J n + 1), ∑ i, e r n i := by
              rw [Finset.mul_sum]
      calc (∑ i, if IsMarkovGood J w e n i then 0 else w n i) / N n
          ≤ (((J n : ℝ) + 1) * ∑ r ∈ Finset.range (J n + 1), ∑ i, e r n i) / N n :=
            div_le_div_of_nonneg_right hsum (hN n)
        _ = levelError N e n (J n) := by
            unfold levelError
            rw [mul_div_assoc, Finset.sum_div]
  · intro r δ hδ
    obtain ⟨K, hK⟩ := exists_nat_gt (1 / δ)
    obtain ⟨M, hM⟩ := hJdiv (max r K)
    refine ⟨M, fun n hn i hgood ↦ ?_⟩
    have hle : max r K ≤ J n := hM n hn
    have hrJ : r ≤ J n := (le_max_left r K).trans hle
    have hKJ : K ≤ J n := (le_max_right r K).trans hle
    have h1 : ((J n : ℝ) + 1) * e r n i ≤ w n i :=
      hgood r (Finset.mem_range.mpr (by omega))
    have hKr : (K : ℝ) ≤ J n := by exact_mod_cast hKJ
    have h2 : 1 < (K : ℝ) * δ := (div_lt_iff₀ hδ).mp hK
    have h3 : (K : ℝ) * δ ≤ ((J n : ℝ) + 1) * δ :=
      mul_le_mul_of_nonneg_right (by linarith) hδ.le
    have h4 : 1 * e r n i ≤ (((J n : ℝ) + 1) * δ) * e r n i :=
      mul_le_mul_of_nonneg_right (by linarith) (he r n i)
    have h5 : δ * (((J n : ℝ) + 1) * e r n i) ≤ δ * w n i :=
      mul_le_mul_of_nonneg_left h1 hδ.le
    linarith

open Classical in
/-- **Diagonal Markov selection** for a countable family of error kinds. -/
theorem exists_isGood {κ : Type*} [Countable κ] [Nonempty κ]
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (N : ℕ → ℝ) (hN : ∀ n, 0 ≤ N n)
    (w : ∀ n, ι n → ℝ) (hw : ∀ n i, 0 ≤ w n i)
    (e : κ → ∀ n, ι n → ℝ) (he : ∀ r n i, 0 ≤ e r n i)
    (hneg : ∀ r, Negligible N fun n ↦ ∑ i, e r n i) :
    ∃ good : ∀ n, ι n → Prop,
      Negligible N (fun n ↦ ∑ i, if good n i then 0 else w n i) ∧
      ∀ (r : κ) (δ : ℝ), 0 < δ →
        ∃ M : ℕ, ∀ n ≥ M, ∀ i, good n i → e r n i ≤ δ * w n i := by
  obtain ⟨φ, hφ⟩ := exists_surjective_nat κ
  obtain ⟨good, hbad, herr⟩ := exists_isGood_nat N hN w hw (fun k ↦ e (φ k))
    (fun k ↦ he (φ k)) (fun k ↦ hneg (φ k))
  refine ⟨good, hbad, fun r δ hδ ↦ ?_⟩
  obtain ⟨k, rfl⟩ := hφ r
  exact herr k δ hδ

end CentralizerNormalizationUniform
end GroupApproximation
