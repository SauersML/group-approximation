import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedOneWordQuotientTest

/-!
# Sentence closure for the uncensused manuscript tail

The current census ends at row 294, but the unchanged manuscript continues
with the displayed one-word quotient test and its two-sentence justification.
This module assigns provisional consecutive sentence anchors 295 and 296 to
that tail and composes the already unconditional exact-route declarations.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

/-- **Tail sentence 295 (`eq:one-word-quotient-test`).** -/
theorem manuscriptSentence295_oneWordQuotientTest :
    PrintedOneWordQuotientTest :=
  manuscriptPrintedOneWordQuotientTest

/-- **Tail sentence 296.**  Every quotient of the visible infinite cyclic
group is MF, while the projection kernel is the normal closure of the one
distinguished defect. -/
theorem manuscriptSentence296_oneWordJustification :
    PrintedOneWordQuotientJustification :=
  manuscriptPrintedOneWordQuotientJustification

/-- The complete uncensused mathematical tail, with no acknowledgment,
methodological, or bibliographic prose encoded as propositions. -/
theorem manuscriptSentenceTailClosure : PrintedOneWordQuotientParagraph :=
  manuscriptPrintedOneWordQuotientParagraph

end OneSidedMFRadical
end Manuscript
end GroupApproximation
