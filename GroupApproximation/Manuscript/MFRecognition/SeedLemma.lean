import GroupApproximation.Manuscript.MFRecognition.SeedPresentation

/-!
# `lem:seed`, as a closed lemma

> **Lemma (`lem:seed`).**  There is a fixed finite presentation `P₋` whose
> group `E = G_{P₋}` is not MF.

The printed proof takes `E` from `[NonMF, Theorem C]`.  In this development
Theorem C is proved along its printed proof from the literature inputs that
its paragraph cites (`NonMF.TorsionFreeTheoremC.manuscriptTorsionFreeFullMFRadical`),
so a seed cut from Theorem C would carry those inputs.  The repository's
closed witness for the lemma is instead the finitely presented non-MF group
`ChosenMarkedPresentation.MarkedGroup`, coded as
`PresentationCodes.negativeCode` and used as the seed of `lem:switch`
(`Switch.seedCode`).  The lemma below is the printed statement with that
witness: a closed proposition, no hypothesis, no construction datum.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Switch

open PresentationCodes

/-- **`lem:seed`, exactly as printed**, as a closed proposition: there is a
finite presentation code whose group is finitely presented and not MF. -/
def PrintedSeed : Prop :=
  ∃ P : PresentationCode,
    Group.IsFinitelyPresented (Carrier P) ∧ ¬ IsOperatorMF (Carrier P)

/-- **`lem:seed` holds**, with the seed code of `lem:switch` as the witness. -/
theorem manuscriptSeed : PrintedSeed :=
  ⟨seedCode, inferInstance, seed_not_isOperatorMF⟩

/-- The seed of the switch is finitely presented and not MF; this is the
form the two branch lemmas consume. -/
theorem seed_finitelyPresented_not_isOperatorMF :
    Group.IsFinitelyPresented H ∧ ¬ IsOperatorMF H :=
  ⟨inferInstance, seed_not_isOperatorMF⟩

end Switch
end MFRecognition
end Manuscript
end GroupApproximation
