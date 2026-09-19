import GroupApproximation.Sofic.LiteralSoficConsequences
import GroupApproximation.Sofic.MFTraceRecognition
import GroupApproximation.Sofic.OperatorMFLocalNormalization
import GroupApproximation.Sofic.CDEOperatorMF
import GroupApproximation.Sofic.ShulmanMFTraceBridge

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

/-! ## The same statement in Shulman's own definition

`markedGroup_not_isMFRegularCharacter` above is stated in the finite-test-set
form on the group unitaries.  `Sofic/ShulmanMFTraceBridge.lean` now closes the
gap to the asymptotic condition on the whole algebra, so the conclusion can be
restated where the literature states it: about the canonical trace of the full
group C⋆-algebra, with the quantifier ranging over every element of `C⋆(E)`
rather than over a finite set of group elements. -/

/-- **The canonical trace of `C⋆(E)` is not an MF trace**, in the sense of
Shulman: there is no sequence of maps `C⋆(E) → M_{kₙ}` that is asymptotically
multiplicative, linear and `*`-preserving in operator norm, uniformly bounded,
and trace-correct.

If there were, `isOperatorMF_of_isMFTrace_canonicalMaximal` would make `E`
operator MF, contradicting Theorem A. -/
theorem markedGroup_canonicalMaximalTrace_not_isMFTrace :
    ¬ ShulmanTrace.IsMFTrace
      (fun a : MaximalGroupCStar MarkedGroup ↦ canonicalMaximalTrace MarkedGroup a) := by
  intro h
  refine LiteralSoficAssembly.markedGroup_finitelyPresented_sofic_nonMF.2.2 ?_
  exact (isCDEOperatorMF_iff_isOperatorMF MarkedGroup).mpr
    (ShulmanTrace.isOperatorMF_of_isMFTrace_canonicalMaximal h)

/-- The half of the trace-class separation that this development proves,
packaged with the facts a reader needs beside it.

`E` is finitely presented, sofic and hyperlinear; `C⋆(E)` is separable; its
canonical trace is a tracial state; and that trace is not MF.  What is *not*
here is the other half — that the same trace is hyperlinear — which needs the
tracial matrix ultraproduct and is deliberately absent. -/
theorem markedGroup_separable_tracialState_not_isMFTrace :
    Group.IsFinitelyPresented MarkedGroup ∧ IsSofic MarkedGroup ∧
      IsHyperlinear MarkedGroup ∧
      TopologicalSpace.SeparableSpace (MaximalGroupCStar MarkedGroup) ∧
      canonicalMaximalTrace MarkedGroup 1 = 1 ∧
      (∀ a b : MaximalGroupCStar MarkedGroup,
        canonicalMaximalTrace MarkedGroup (a * b)
          = canonicalMaximalTrace MarkedGroup (b * a)) ∧
      ¬ ShulmanTrace.IsMFTrace
        (fun a : MaximalGroupCStar MarkedGroup ↦ canonicalMaximalTrace MarkedGroup a) :=
  ⟨LiteralSoficAssembly.markedGroup_finitelyPresented_sofic_nonMF.1,
    LiteralSoficAssembly.markedGroup_isSofic,
    LiteralSoficAssembly.markedGroup_isHyperlinear,
    maximalGroupCStar_separableSpace MarkedGroup,
    (canonicalMaximalTrace_isTracialState MarkedGroup).1,
    (canonicalMaximalTrace_isTracialState MarkedGroup).2.2,
    markedGroup_canonicalMaximalTrace_not_isMFTrace⟩

end LiteralTraceConsequence
end GroupApproximation
