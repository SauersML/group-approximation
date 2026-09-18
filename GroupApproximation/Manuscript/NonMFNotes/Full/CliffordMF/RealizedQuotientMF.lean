import GroupApproximation.Manuscript.NonMFNotes.Full.CliffordMF.LampKernel
import GroupApproximation.Manuscript.NonMFNotes.Full.TWW.SubgroupRegularModels
import TWWCYCLIC_MODULE

/-!
# The realized Clifford quotient is MF

This file serves `non_mf_group_notes.tex`, `\section{Necessity}`, paragraph
*Sharpness of the Kazhdan hypothesis* (tex ≈ 1163–1170), clause "So it is MF".

The realized quotient `LiteralDyadicCalibration.DyadicRealizedQuotient` is countable and
amenable. Its lamp kernel is locally finite with solvable quotient
(`CliffordMF.LampKernel`). The solvable-quotient induction of `Full.TWW` therefore
upgrades the locally finite base case to regular-character models on the whole group,
and those models make the group operator MF.
-/

namespace GroupApproximation.Full.NN10b

open GroupApproximation.LiteralDyadicCalibration GroupApproximation.Full.TWW

/-- **The realized Clifford quotient is MF** (`non_mf_group_notes.tex`, sharpness
paragraph, "So it is MF"). -/
theorem dyadicRealizedQuotient_isOperatorMF : IsOperatorMF DyadicRealizedQuotient :=
  isOperatorMF_of_isModelled_top
    (of_isSolvable_quotient isSequentialUnionClosed_isModelled
      (isCyclicExtensionClosed_isModelled isAmenable_dyadicRealizedQuotient)
      (lampKernel dyadicRealization.range)
      (isModelled_of_isLocallyFiniteGroup (isLocallyFiniteGroup_lampKernel _)))

end GroupApproximation.Full.NN10b
