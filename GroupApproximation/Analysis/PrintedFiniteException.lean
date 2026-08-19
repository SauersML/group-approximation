import GroupApproximation.Analysis.PrintedLiftingSteps

/-!
# "Set `uₙ = 1` at the finitely many remaining indices", with the set formed

Proof-ledger row `PRE.11`, the closing move of the printed proof of `lem:lift`
in `non_mf_groups_exist.tex`:

> … set `uₙ = 1` at the finitely many remaining indices.

`Analysis/PrintedLiftingSteps` names the two branches of the printed patched
sequence — `polarPatch_eq_polarCorrect` on the good set, `polarPatch_eq_one`
off it — and `exists_boundedLift_polarPatch` walks `lem:lift` through the four
printed moves.  What the ledger row records as missing is smaller and exactly
one sentence: the printed step is about a **finite exceptional set**, and the
existing route never forms one — it requires the Gram estimate only on a
member of the cofinite filter, which is stronger and silently so.

This file forms the set.  `remainingIndices_finite` is *"the finitely many
remaining indices"* as an object: the set of indices where the Gram defect of
the lift exceeds `1/2` is finite, which is literally what membership of the
good set in the `cofinite` filter says.  `manuscriptFiniteExceptionPatch` is
the printed sentence assembled: a bounded lift of the given corona unitary
whose exceptional set is finite, whose patched sequence is `1` exactly on that
finite set and the printed polar correction off it, and whose patched class is
the unitary that was lifted.
-/

namespace GroupApproximation
namespace PrintedFiniteException

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]

omit [∀ n, Nonempty (X n)] in
/-- **"The finitely many remaining indices", formed.**  If the Gram defect of
a bounded lift is eventually at most `1/2` along `cofinite`, then the set of
remaining indices — those where it exceeds `1/2` — is finite.  This is the
definition of the `cofinite` filter, stated so the printed finite exceptional
set is an object rather than a filter membership. -/
theorem remainingIndices_finite (a : BoundedMatrixSequence (fun n ↦ X n))
    (hgood : ∀ᶠ n in cofinite,
      ‖KazhdanCornerMatrices.cornerGram (a n) - 1‖ ≤ (1 / 2 : ℝ)) :
    {n : ℕ |
      ¬ ‖KazhdanCornerMatrices.cornerGram (a n) - 1‖ ≤ (1 / 2 : ℝ)}.Finite :=
  Filter.eventually_cofinite.mp hgood

/-- **The printed step, assembled.**  Every unitary of the corona has a
bounded lift `a` such that: the class of `a` is the unitary; the exceptional
set — the printed *"finitely many remaining indices"* — is finite; the printed
patched sequence is `1` at every index of that finite set and the printed
polar correction everywhere else; and the class of the patched sequence is
the unitary that was lifted.  This is `PRE.11` with the finite set formed
rather than replaced by a filter membership. -/
theorem manuscriptFiniteExceptionPatch
    (x : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
    ∃ a : BoundedMatrixSequence (fun n ↦ X n),
      normMatrixCStarCoronaMk (fun n ↦ X n) a =
          (x : NormMatrixCStarCorona (fun n ↦ X n)) ∧
        {n : ℕ | ¬ ‖KazhdanCornerMatrices.cornerGram (a n) - 1‖
          ≤ (1 / 2 : ℝ)}.Finite ∧
        (∀ n, ¬ ‖KazhdanCornerMatrices.cornerGram (a n) - 1‖ ≤ (1 / 2 : ℝ) →
          PrintedLiftingSteps.polarPatch X a n = 1) ∧
        (∀ n, (hn : ‖KazhdanCornerMatrices.cornerGram (a n) - 1‖
            ≤ (1 / 2 : ℝ)) →
          PrintedLiftingSteps.polarPatch X a n =
            KazhdanCornerMatrices.polarCorrectUnitary (a n)
              (KazhdanCornerMatrices.cornerGram_isHermitian (a n)) hn le_rfl) ∧
        unitarySequenceToCorona X (PrintedLiftingSteps.polarPatch X a) = x := by
  obtain ⟨a, ha, hgood, hclass⟩ :=
    PrintedLiftingSteps.exists_boundedLift_polarPatch X x
  exact ⟨a, ha, remainingIndices_finite X a hgood,
    fun n hn ↦ PrintedLiftingSteps.polarPatch_eq_one X a hn,
    fun n hn ↦ PrintedLiftingSteps.polarPatch_eq_polarCorrect X a hn,
    hclass⟩

end

end PrintedFiniteException
end GroupApproximation
