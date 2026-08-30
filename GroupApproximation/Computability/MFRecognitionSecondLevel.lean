import GroupApproximation.Computability.HereditaryPropertySwitchCompleteness
import GroupApproximation.Computability.MFRecognitionImpossible
import GroupApproximation.Computability.MFRecognitionPi02

/-!
# The computability endpoint for second-level MF recognition

This file contains no operator-algebra or HNN argument.  It isolates the
purely computability-theoretic last step of the finite-presentation
classification.

The checker theorem in `MFRecognitionPi02` already places MF recognition in
`Pi02`.  The event-switch framework says that one computable finite-output
compiler with the exact `INF` truth table makes the predicate `Pi02`-hard.
Once those two statements are combined, complementation supplies the entire
`Sigma02` classification of non-MF recognition with the *same* reduction.

Consequently the only input below is the concrete finite-presentation
compiler.  There is no second, hidden compiler obligation for the negative
side, and no additional analytic permanence statement occurs in this file.
-/

namespace GroupApproximation
namespace MFRecognitionSecondLevel

open ArithmeticalHierarchy PresentationCodes
open HereditaryPropertySwitchCompleteness

/-- Operator-MF as a predicate on the repository's concrete recursive type
of finite-presentation codes. -/
abbrev MFCode (c : PresentationCode) : Prop :=
  IsOperatorMF (Carrier c)

/-- The literal complement of `MFCode`; this is the finite-presentation
non-MF recognition problem. -/
abbrev NonMFCode (c : PresentationCode) : Prop :=
  ¬ MFCode c

/-- The finite-presentation MF predicate has the unconditional second-level
universal upper bound supplied by the concrete matrix checker. -/
theorem mfCode_pi02 : Pi02 MFCode := by
  change Pi02 (fun c : PresentationCode ↦ IsOperatorMF (Carrier c))
  exact MFRecognitionPi02.operatorMFCode_pi02

/-- Complementing the same checker gives the unconditional second-level
existential upper bound for non-MF recognition. -/
theorem nonMFCode_sigma02 : Sigma02 NonMFCode := by
  change Sigma02 (fun c : PresentationCode ↦ ¬ IsOperatorMF (Carrier c))
  exact MFRecognitionPi02.nonOperatorMFCode_sigma02

/-- The exact finite-output compiler datum needed by the hardness proof.
Its correctness clause says that the compiled finite presentation is MF
exactly when the source partial program has infinite domain. -/
abbrev MFCompiler :=
  FinitePresentationSwitchCompiler OperatorMFProperty

/-- A finite-output switch compiler, together with the unconditional checker
upper bound, proves the exact `Pi02` classification of MF recognition on
finite presentations. -/
theorem mfCode_pi02Complete_of_compiler (C : MFCompiler) :
    Pi02Complete MFCode := by
  change Pi02Complete
    (AdianRabinGeneral.codeProperty OperatorMFProperty)
  exact ⟨mfCode_pi02,
    (finiteOutput_switch_completeness_package C).2.2.1⟩

/-- The reverse classification needs no new construction: complementing the
same many-one reductions proves `Sigma02`-completeness of non-MF
recognition. -/
theorem nonMFCode_sigma02Complete_of_compiler (C : MFCompiler) :
    Sigma02Complete NonMFCode := by
  simpa only [NonMFCode] using
    (pi02Complete_compl (mfCode_pi02Complete_of_compiler C))

/-- Both exact hierarchy classifications, packaged with the already proved
algorithmic impossibility statements.  The last two conjuncts are
unconditional: the compiler is used only for the optimal second-level lower
bounds. -/
theorem finitePresentationMF_secondLevel_package (C : MFCompiler) :
    Pi02Complete MFCode ∧
      Sigma02Complete NonMFCode ∧
      ¬ ComputablePred MFCode ∧
      ¬ REPred NonMFCode := by
  exact ⟨mfCode_pi02Complete_of_compiler C,
    nonMFCode_sigma02Complete_of_compiler C,
    MFRecognitionImpossible.mf_recognition_not_computable,
    MFRecognitionImpossible.nonMF_presentations_not_re⟩

/-- Boolean-decider formulation of the no-algorithm consequence. -/
theorem no_finitePresentation_MF_decider :
    ¬ ∃ f : PresentationCode → Bool,
      Computable f ∧ ∀ c, f c = true ↔ MFCode c := by
  simpa only [MFCode] using MFRecognitionImpossible.no_mf_decider

end MFRecognitionSecondLevel
end GroupApproximation
