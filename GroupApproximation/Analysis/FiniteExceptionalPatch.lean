import GroupApproximation.Analysis.PrintedLiftingSteps

/-!
# `PRE.11`: the finite exceptional set, formed

Proof-ledger row `PRE.11`, `lem:lift`: *"set `uₙ = 1` at the finitely many
remaining indices."*  The row's note holds the grade at MISMATCH because "the
printed sentence is a step about a finite exceptional set and the Lean route
never forms one": `Analysis/PrintedLiftingSteps.lean` patches along the
cofinite filter, whose complement member is never exhibited as a finite set.

This module forms it.  `exceptionalSet` is the set of indices where the Gram
defect of the chosen bounded lift exceeds `1/2` — the indices the printed
sentence patches — and for a lift of a corona unitary it is **finite**
(`exceptionalSet_finite`), which is the words "the finitely many remaining
indices" as a statement.  `exists_boundedLift_finite_exceptional_patch`
restates `lem:lift` through the four printed moves with the finite set
explicit: the patched sequence is the polar correction off the finite
exceptional set (`polarPatch_eq_polarCorrect_off_exceptional`), is `1` on it
(`polarPatch_eq_one_on_exceptional`), and represents the given unitary.

Nothing analytic is new: the content is `PrintedLiftingSteps`', and the filter
argument is unchanged — `Filter.eventually_cofinite` is the passage between
"eventually along `cofinite`" and "off a finite set", which is what the row
said was missing.
-/

namespace GroupApproximation
namespace FiniteExceptionalPatch

open Filter PrintedLiftingSteps
open scoped Matrix.Norms.L2Operator ENNReal

variable (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]

noncomputable section

/-- **The exceptional set** of a bounded lift: the indices where the Gram
defect exceeds `1/2`, i.e. the "remaining indices" at which the printed proof
sets `uₙ = 1`. -/
def exceptionalSet (a : BoundedMatrixSequence (fun n ↦ X n)) : Set ℕ :=
  {n | ¬ ‖KazhdanCornerMatrices.cornerGram (a n) - 1‖ ≤ (1 / 2 : ℝ)}

/-- **"The finitely many remaining indices"**: for a bounded lift of a corona
unitary, the exceptional set is finite. -/
theorem exceptionalSet_finite {a : BoundedMatrixSequence (fun n ↦ X n)}
    (ha : star (normMatrixCStarCoronaMk (fun n ↦ X n) a) *
        normMatrixCStarCoronaMk (fun n ↦ X n) a = 1) :
    (exceptionalSet X a).Finite := by
  have hgood : ∀ᶠ n in cofinite,
      ‖KazhdanCornerMatrices.cornerGram (a n) - 1‖ ≤ (1 / 2 : ℝ) := by
    have hnear := (Metric.tendsto_nhds.mp (gramDefect_tendsto_zero X ha))
      (1 / 2 : ℝ) (by norm_num)
    filter_upwards [hnear] with n hn
    simpa only [Real.dist_eq, sub_zero, abs_norm] using hn.le
  exact eventually_cofinite.mp hgood

omit [∀ n, Nonempty (X n)] in
/-- On the exceptional set the patched sequence is the identity: the literal
"set `uₙ = 1`". -/
theorem polarPatch_eq_one_on_exceptional
    (a : BoundedMatrixSequence (fun n ↦ X n)) {n : ℕ}
    (hn : n ∈ exceptionalSet X a) :
    polarPatch X a n = 1 :=
  polarPatch_eq_one X a hn

omit [∀ n, Nonempty (X n)] in
/-- Off the exceptional set the patched sequence is the printed polar
correction. -/
theorem polarPatch_eq_polarCorrect_off_exceptional
    (a : BoundedMatrixSequence (fun n ↦ X n)) {n : ℕ}
    (hn : n ∉ exceptionalSet X a) :
    polarPatch X a n =
      KazhdanCornerMatrices.polarCorrectUnitary (a n)
        (KazhdanCornerMatrices.cornerGram_isHermitian (a n))
        (not_not.mp hn) le_rfl :=
  polarPatch_eq_polarCorrect X a (not_not.mp hn)

/-- **`lem:lift` with the finite exceptional set explicit.**  Every unitary of
the corona is represented by the patched polar correction of a bounded lift,
where the patching happens on a set of indices that is exhibited as finite —
the printed sentence's "set `uₙ = 1` at the finitely many remaining
indices". -/
theorem exists_boundedLift_finite_exceptional_patch
    (x : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
    ∃ a : BoundedMatrixSequence (fun n ↦ X n),
      normMatrixCStarCoronaMk (fun n ↦ X n) a =
          (x : NormMatrixCStarCorona (fun n ↦ X n)) ∧
        (exceptionalSet X a).Finite ∧
        (∀ n ∈ exceptionalSet X a, polarPatch X a n = 1) ∧
        unitarySequenceToCorona X (polarPatch X a) = x := by
  obtain ⟨a, ha, hgood, hclass⟩ := exists_boundedLift_polarPatch X x
  exact ⟨a, ha, eventually_cofinite.mp hgood,
    fun n hn ↦ polarPatch_eq_one X a hn, hclass⟩

end

end FiniteExceptionalPatch
end GroupApproximation
