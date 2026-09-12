import GroupApproximation.Manuscript.OneSidedMFRadical.PartialClosureLeavitt
import GroupApproximation.Meta.AxiomGuard

/-!
# Closed audit of the explicit simplicity case calculations

These are the current proof's diagonal conjugation calculation and its sparse
and dense off-diagonal matrix calculations.  The superseded coefficient-
separation construction in the imported source is intentionally not part of
this audit; the current two-sandwich proof is audited separately in
`SentenceSimplifiedCoefficientSeparationClosure`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

#audit_closed_axioms manuscriptPrintedDiagonalConjugationMovesRoot
#audit_closed_axioms manuscriptPrintedDiagonalConjugationMovesRootAtBinaryLeavitt
#audit_closed_axioms manuscriptPrintedSparseDefectEntryNonzero
#audit_closed_axioms manuscriptPrintedDenseAnnihilatingProduct

end OneSidedMFRadical
end Manuscript
end GroupApproximation
