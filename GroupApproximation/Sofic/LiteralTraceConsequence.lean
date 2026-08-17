import GroupApproximation.Sofic.LiteralSoficAssembly
import GroupApproximation.Sofic.MFTraceRecognition
import GroupApproximation.Sofic.OperatorMFLocalNormalization
import GroupApproximation.Sofic.CDEOperatorMF

/-!
# The regular character of the literal group is not an MF trace

`Sofic/MFTraceRecognition.lean` proves that a group whose regular character
admits trace-correct operator-norm matrix models is operator MF: the trace
clause at `1` pins a macroscopic unit corner, and the trace clause away from
`1` supplies separation.  The literal finitely presented group `E` of
`Sofic/LiteralNonMFPresentation.lean` is not operator MF, so it admits no
such models.

This is the trace-level form of Theorem A, and it is one composition with no
new analysis in it.  The recognition theorem contributes the corner rounding
and the polar correction; `Sofic/LiteralSoficAssembly.lean` contributes the
group.

## What this is, and what it is not

`MFTraceRecognition.IsMFRegularCharacter` is the finite-test-set condition on
the *group unitaries*: a norm bound, operator-norm multiplicativity and
star-compatibility on a test set, and trace-correctness at `1` and away from
`1`.  It is the local form of the MF-trace condition for the canonical trace
of the full group `C^*`-algebra.

It is **not** the asymptotic condition on the whole of `C^*(E)`.  Relating the
two is a definitional comparison, and it is deliberately not carried out here;
the manuscript states the comparison in prose and does not badge it.
-/

namespace GroupApproximation
namespace LiteralTraceConsequence

open LiteralNonMFPresentation

/-- **The regular character of the literal group `E` is not an MF trace.**

If it were, the corner-and-polar correction of `MFTraceRecognition` would
produce operator-norm local models with separation constant `1`, hence an
operator-MF structure on `E`, contradicting Theorem A. -/
theorem markedGroup_not_isMFRegularCharacter :
    ¬ MFTraceRecognition.IsMFRegularCharacter MarkedGroup := by
  intro h
  refine LiteralSoficAssembly.markedGroup_finitelyPresented_sofic_nonMF.2.2 ?_
  refine (isCDEOperatorMF_iff_isOperatorMF MarkedGroup).mpr ?_
  refine OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one.mpr ?_
  exact MFTraceRecognition.isNormApproximable_of_isMFRegularCharacter MarkedGroup h

/-- The separation packaged with the group facts the manuscript prints beside
it: `E` is finitely presented, sofic, hyperlinear, and its regular character
is not an MF trace. -/
theorem markedGroup_sofic_hyperlinear_not_isMFRegularCharacter :
    Group.IsFinitelyPresented MarkedGroup ∧ IsSofic MarkedGroup ∧
      IsHyperlinear MarkedGroup ∧
      ¬ MFTraceRecognition.IsMFRegularCharacter MarkedGroup :=
  ⟨LiteralSoficAssembly.markedGroup_finitelyPresented_sofic_nonMF.1,
    LiteralSoficAssembly.markedGroup_isSofic,
    LiteralSoficAssembly.markedGroup_isHyperlinear,
    markedGroup_not_isMFRegularCharacter⟩

end LiteralTraceConsequence
end GroupApproximation
