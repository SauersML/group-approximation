import GroupApproximation.GGT.RelHypOsin24RelativeWordSpelling

/-!
# The metric-to-pattern pigeonhole step

The finite base converts a bounded displacement in the relative Cayley graph to
a natural bound on `wordNorm`.  The labelled-word lift then supplies relative
spellings, and the finite-pattern theorem gives an infinite subfamily with one
fixed labelled skeleton.  This is the complete combinatorial prefix of Osin's
bounded-power argument.

The source correspondence is the finite-word part of the proof of Memoirs
Theorem 1.10 (before Lemmas `cyc1`, `qc1`, and `qc-hyp`).  The remaining step,
which uses relative components and the centralizer/quasi-convexity estimate,
is exactly the named `RelativeBoundedPowerExtractionStatement`.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-- A bounded metric power family has an infinite subfamily of one fixed
labelled relative-word pattern.  The admissible spellings are produced from
the metric bound, not assumed. -/
def MetricBoundedRepeatedRelativePatternStatement : Prop :=
  ∀ (G : Type u) (_ : Group G) (I : Type v) [Finite I]
    (D : RelGenSet G I),
    D.base.Finite → ∀ (g : G) (R : ℝ) (S : Set ℕ), S.Infinite →
      (∀ q : ℕ, q ∈ S →
        dist (Cayley.base D.alphabet) ((g ^ q) • Cayley.base D.alphabet) ≤ R) →
      ∃ N : ℕ, ∃ p : RelativeWordPattern G I, ∃ T : Set ℕ,
        T ⊆ S ∧ T.Infinite ∧
          ∀ q : ℕ, q ∈ T → ∃ w : List (RelLetter G I),
            (∀ a ∈ w, D.IsLetter a) ∧ w.length ≤ N ∧
              relativeWordPattern w = p ∧ RelLetter.listVal w = g ^ q

theorem metricBoundedRepeatedRelativePattern_proved :
    MetricBoundedRepeatedRelativePatternStatement.{u, v} := by
  intro G instG I _ D hbase g R S hS hbounded
  letI : Group G := instG
  obtain ⟨N, hRN⟩ := exists_nat_gt R
  have hwords : ∀ q : ℕ, q ∈ S →
      ∃ w : List (RelLetter G I),
        (∀ a ∈ w, D.IsLetter a) ∧ w.length ≤ N ∧
          RelLetter.listVal w = g ^ q := by
    intro q hq
    have hdist :
        dist (Cayley.base D.alphabet) ((g ^ q) • Cayley.base D.alphabet) =
          ((wordNorm D.alphabet.carrier (g ^ q) : ℕ) : ℝ) := by
      rw [Cayley.dist_eq, Cayley.val_smul, Cayley.val_base, mul_one,
        wordDist_one_left]
    have hreal :
        ((wordNorm D.alphabet.carrier (g ^ q) : ℕ) : ℝ) < (N : ℝ) := by
      exact lt_of_le_of_lt (by simpa [← hdist] using hbounded q hq) hRN
    have hnat : wordNorm D.alphabet.carrier (g ^ q) < N := by
      exact_mod_cast hreal
    exact relativeWordSpelling_proved G instG I D (g ^ q) N
      (Nat.le_of_lt hnat)
  obtain ⟨p, T, hTS, hT, hpat⟩ :=
    infiniteRepeatedRelativePattern_proved G instG I D hbase N g S hS hwords
  exact ⟨N, p, T, hTS, hT, hpat⟩

/-- Trivial-group model test.  The premise supplies a bounded orbit, and the
empty labelled spelling gives the repeated pattern. -/
theorem metricBoundedRepeatedRelativePattern_trivialModel
    {I : Type v} [Finite I] (D : RelGenSet PUnit I) (hbase : D.base.Finite)
    (g : PUnit) (R : ℝ) (S : Set ℕ) (hS : S.Infinite)
    (hbounded : ∀ q : ℕ, q ∈ S →
      dist (Cayley.base D.alphabet) ((g ^ q) • Cayley.base D.alphabet) ≤ R) :
    ∃ N : ℕ, ∃ p : RelativeWordPattern PUnit I, ∃ T : Set ℕ,
      T ⊆ S ∧ T.Infinite ∧
        ∀ q : ℕ, q ∈ T → ∃ w : List (RelLetter PUnit I),
          (∀ a ∈ w, D.IsLetter a) ∧ w.length ≤ N ∧
            relativeWordPattern w = p ∧ RelLetter.listVal w = g ^ q :=
  metricBoundedRepeatedRelativePattern_proved PUnit inferInstance I D hbase
    g R S hS hbounded

end RelHyp
end GGT
end GroupApproximation
