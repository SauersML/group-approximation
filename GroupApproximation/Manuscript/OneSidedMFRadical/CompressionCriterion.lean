import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedCriterion

/-!
# The complete printed one-sided compression criterion

`PrintedCriterion` proves the three MF-radical clauses of
Theorem~`thm:compression-criterion`, while `PrintedDefect` proves its final,
independent finite-dimensional-representation clause.  The manuscript prints
all four in one theorem, so this module exposes their conjunction as one
closed endpoint for the current-manuscript audit.

Both constituents use `printedDefect`, the normal closure indexed by
individual one-sided compressors.  Thus this endpoint has exactly the defect
quantification in `non_mf_groups_exist.tex`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

/-- Theorem~`thm:compression-criterion` in its complete printed form. -/
def CompleteOneSidedCompressionCriterion : Prop :=
  OneSidedCompressionCriterion ∧
    PrintedDefectFiniteDimensionalSterility.{0, 0, 0}

/-- Closed proof of every clause of the printed one-sided compression
criterion. -/
theorem manuscriptCompleteOneSidedCompressionCriterion :
    CompleteOneSidedCompressionCriterion :=
  ⟨manuscriptOneSidedCompressionCriterion,
    manuscriptPrintedDefectFiniteDimensionalSterility.{0, 0, 0}⟩

end OneSidedMFRadical
end Manuscript
end GroupApproximation
