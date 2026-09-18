import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ExtensionAbsorbIsometryFixCore
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.StdOperatorAlgebraComplete

/-!
# Every near isometry is a compact perturbation of an isometry

Lane `TWWSch3c2-C3b`, work order `WO-TWWSch-3c2-C3b`. Sources: G. A. Elliott and D. Kucerovsky,
Pacific J. Math. 198 (2001), proof of Thm. 6; G. J. Murphy, *C⋆-algebras and operator theory*,
Thm. 2.1.13. Manuscript label: `non_mf_group_notes.tex`, `thm:fixed-radical-membership`.

`ExtensionAbsorbIsometryFixCore` proves the statement assuming `StdBdd J` is complete. That
completeness is the instance `CompleteSpace (StdBdd J)` from `StdOperatorAlgebraComplete`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- **Polar correction of a near isometry.** Every near isometry `w` of `H_J` is a compact
perturbation of the isometry `w' = w (w⋆w)^{-1/2}` (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`; Elliott–Kucerovsky 2001, proof of Thm. 6). -/
theorem exists_isometry_compactEq_of_isStdNearIsometry {w : StdBdd J} (hw : IsStdNearIsometry w) :
    ∃ w' : StdBdd J, star w' * w' = 1 ∧ CompactEq J w'.1 w.1 :=
  exists_isometry_compactEq_of_isStdNearIsometry_of_completeSpace hw

end GroupApproximation.Full.TWWSchafhauser
