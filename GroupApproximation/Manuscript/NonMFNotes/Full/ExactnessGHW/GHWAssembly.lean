import GroupApproximation.Manuscript.NonMFNotes.Full.ExactnessGHW.GridCoarse
import GroupApproximation.Manuscript.NonMFNotes.Full.ExactnessGHW.BorelSolvable
import GroupApproximation.Manuscript.NonMFNotes.Full.ExactnessGHW.GridApproximation
import GroupApproximation.Manuscript.NonMFNotes.Full.ExactnessGHW.VerticalAssembly
import Mathlib.Tactic.Choose

/-!
# Exactness of `Σ` and of the literal marked group

`non_mf_group_notes.tex`, paragraph `\paragraph{Exactness.}` after
`prop:blocknormalform`: `Σ = gammaBar ≤ GL₄(ℚ)` is integral and uniformly close to
dyadic grid points of the solvable Borel subgroup (Guentner--Higson--Weinberger),
hence has property A; the permanence steps of `VerticalAssembly` then give
exactness of the literal marked group `E`.
-/

namespace GroupApproximation.Full.NN09b

open GroupApproximation.ExplicitLinearModel GroupApproximation.ExactnessPermanence

/-- **`Σ` has property A** (Guentner--Higson--Weinberger). -/
theorem hasPropertyA_gammaBar : HasPropertyA gammaBar := by
  obtain ⟨c, hc⟩ := exists_gridPoint_near
  choose b hb hbc using hc
  exact hasPropertyA_of_gridApprox gammaBar (fun _ h ↦ gammaBar_isIntegralUnit h) c b hb hbc
    (hasPropertyA_of_isSolvable borel)

/-- **The literal marked group is exact.** `non_mf_group_notes.tex`,
`\paragraph{Exactness.}`. -/
theorem markedGroup_isExactGroup : IsExactGroup LiteralNonMFPresentation.MarkedGroup :=
  markedGroup_isExactGroup_of_gammaBar hasPropertyA_gammaBar

/-- The marked-compression witness group has property A. -/
theorem hasPropertyA_witnessGroup : HasPropertyA LiteralNonMFLinearWitness.WitnessGroup :=
  hasPropertyA_witnessGroup_of_gammaBar hasPropertyA_gammaBar

end GroupApproximation.Full.NN09b
