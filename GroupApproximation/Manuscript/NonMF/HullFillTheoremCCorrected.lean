import GroupApproximation.Manuscript.NonMF.HullFillCorrectedInputs
import GroupApproximation.Manuscript.NonMF.TheoremCPrinted

/-!
# The corrected Theorem C, as it was routed before the substitution was made in
place

`Manuscript.NonMF.HullFillKernelRefutation` refutes one field of
`TorsionFree.HullInputs`, and `Manuscript.NonMF.HullFillCorrectedInputs`
replaces the bundle by `HullInputsCorrected`.  While `Saturation.saturation`
still took the refuted bundle, this module carried the printed proof of
Theorem C over to the corrected one, by re-proving it with the single call to
`lem:saturation` supplied from the corrected bundle.

That substitution has since been made where it belongs:
`Saturation.saturation`, `TorsionFreeTheoremC.manuscriptTorsionFreeFullMFRadical`
and `TheoremCPrinted.manuscriptTorsionFreeSimplified` take
`HullInputsCorrected` themselves, and `Manuscript.NonMF.TheoremCAssembly` closes
the two printed forms on `TorsionFree.hullInputs : HullInputsCorrected`.  So the
two theorems here are now aliases of the printed ones, kept because reports and
messages of this lane name them, and because deleting a module means deleting a
line of the root import list, which is how `main` gets broken.  Nothing in the
repository consumes them.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace HullCorrectedInputs

open GroupApproximation.Manuscript.NonMF.TheoremC

/-- **`thm:torsion-free` (Theorem C), as printed, from the corrected Hull
bundle.**  An alias of `TorsionFreeTheoremC.manuscriptTorsionFreeFullMFRadical`,
which takes that bundle itself. -/
theorem manuscriptTorsionFreeFullMFRadical_corrected (I : LiteratureInputs)
    (hHull : HullInputsCorrected.{0}) :
    PrintedTorsionFreeFullMFRadical :=
  manuscriptTorsionFreeFullMFRadical I hHull

/-- **Theorem C in the simplified printed statement, from the corrected Hull
bundle.**  An alias of `TheoremCPrinted.manuscriptTorsionFreeSimplified`. -/
theorem manuscriptTorsionFreeSimplified_corrected (I : LiteratureInputs)
    (hHull : HullInputsCorrected.{0}) : PrintedTorsionFreeSimplified :=
  manuscriptTorsionFreeSimplified I hHull

end HullCorrectedInputs
end NonMF
end Manuscript
end GroupApproximation
