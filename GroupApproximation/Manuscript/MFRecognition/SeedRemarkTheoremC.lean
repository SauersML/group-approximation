import GroupApproximation.Manuscript.MFRecognition.SeedPresentation
import GroupApproximation.Manuscript.MFRecognition.SeedFromTheoremC

/-!
# `lem:seed` as printed: the Theorem C seed

`SeedPresentation` runs the FIN/INF switch on the repository's closed
negative presentation code, which is non-MF with no hypothesis.  The printed
proof of `lem:seed` takes its seed from Theorem C instead.  This module
records that reading, and it is the only place where the two meet.

The seeds are interchangeable: `lem:switch` and both branch lemmas use only
that the seed is finitely presented and not MF, and neither reads the code
itself.  Keeping the printed reading here rather than in `SeedPresentation`
keeps `Manuscript.NonMF.TheoremCDebts` out of the import closure of the
recognition chain, so that chain neither depends on Theorem C's recorded
debts nor fails to build with them.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Switch

open PresentationCodes

/-- **`lem:seed` as printed**: the group of Theorem C is a finitely presented
non-MF seed as well, on Theorem C's recorded debts.  Interchangeable with
`seedCode`, which carries no debt. -/
theorem seedCodeC_not_isOperatorMF :
    ¬ IsOperatorMF (Carrier SeedFromTheoremC.seedCodeC) :=
  SeedFromTheoremC.not_isOperatorMF_seedCodeC

end Switch
end MFRecognition
end Manuscript
end GroupApproximation
