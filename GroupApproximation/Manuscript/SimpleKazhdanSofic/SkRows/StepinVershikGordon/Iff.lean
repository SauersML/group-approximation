import GroupApproximation.Manuscript.SimpleKazhdanSofic.QuestionsNotFinitelyPresented
import GroupApproximation.Sofic.LEFSofic
import GroupApproximation.Dynamics.SurjunctivityTransfer
import GroupApproximation.Meta.AxiomGuard

/-!
# Stepin / Vershik–Gordon as an equivalence

`simple_kazhdan_sofic_group.tex`, section `sec:questions` (tex l.730–732):

> No group in Theorem~\ref{thm:general}\textup{(b)} is finitely presented:
> a finitely presented LEF group is residually
> finite~\cite{Stepin,VershikGordon}, and an infinite simple group is not.

The cited fact is one direction of an equivalence: for a finitely presented group, LEF and
residually finite coincide.

## Route

* LEF ⇒ RF (the cited Stepin / Vershik–Gordon theorem): the closed corpus theorem
  `SimpleKazhdanSofic.printedFinitelyPresentedLEFResiduallyFinite`
  (`QuestionsNotFinitelyPresented.lean`), itself from `finitelyPresented_isLEF_residuallyFinite`
  over `PresentedGroup` of a finite relator set.
* RF ⇒ LEF (no presentation needed): `isLEF_of_residuallyFinite` (`Sofic/LEFSofic.lean`), stated
  for Mathlib's `Group.ResiduallyFinite`, transported along
  `isResiduallyFinite_iff_group_residuallyFinite` (`Dynamics/SurjunctivityTransfer.lean`).

The sharpness of the finite-presentation hypothesis is `Sharpness.lean`.
-/

namespace GroupApproximation.SimpleKazhdanSofic.SkRows.StepinVershikGordon

open GroupApproximation GroupApproximation.SimpleKazhdanSofic

universe u

/-- **Residually finite groups are LEF**, for the repository predicate `IsResiduallyFinite`. -/
theorem isLEF_of_isResiduallyFinite {G : Type u} [Group G] (hrf : IsResiduallyFinite G) :
    IsLEF G := by
  haveI : Group.ResiduallyFinite G := isResiduallyFinite_iff_group_residuallyFinite.mp hrf
  exact isLEF_of_residuallyFinite

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.StepinVershikGordon.isLEF_of_isResiduallyFinite

/-- **tex l.731, as an equivalence** [Stepin, Vershik–Gordon]: a finitely presented group is LEF
if and only if it is residually finite. -/
theorem manuscriptSentence_finitelyPresentedLEFIffResiduallyFinite {G : Type u} [Group G]
    (hfp : Group.IsFinitelyPresented G) : IsLEF G ↔ IsResiduallyFinite G :=
  ⟨printedFinitelyPresentedLEFResiduallyFinite.{u} G hfp, isLEF_of_isResiduallyFinite⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.StepinVershikGordon.manuscriptSentence_finitelyPresentedLEFIffResiduallyFinite

/-- The same equivalence with Mathlib's `Group.ResiduallyFinite`. -/
theorem finitelyPresented_isLEF_iff_group_residuallyFinite {G : Type u} [Group G]
    (hfp : Group.IsFinitelyPresented G) : IsLEF G ↔ Group.ResiduallyFinite G :=
  (manuscriptSentence_finitelyPresentedLEFIffResiduallyFinite hfp).trans
    isResiduallyFinite_iff_group_residuallyFinite

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.StepinVershikGordon.finitelyPresented_isLEF_iff_group_residuallyFinite

end GroupApproximation.SimpleKazhdanSofic.SkRows.StepinVershikGordon
