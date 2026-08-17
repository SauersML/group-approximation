import GroupApproximation

/-!
# Kernel audit of Theorem E: a finitely presented sofic/hyperlinear non-MF group

Run with:

    lake env lean scratch/TheoremEAudit.lean

Two independent checks, both of which must pass for the manuscript's
Theorem E to be "fully formalized, no-input proven".

1. **Statement pinning.**  Each `example` below restates the badged
   declaration verbatim, with no hypothesis and no free variable.  If any
   of the four gains a premise or is weakened, one of these fails to
   elaborate.  Note in particular that every statement is a closed term:
   `MarkedGroup` is a concrete `PresentedGroup` on the 41 relators, not a
   variable, so none of these is schematic.

2. **Transitive axiom closure.**  `#print axioms` must report exactly

       [propext, Classical.choice, Quot.sound]

   for all four.  Anything else -- `sorryAx`, `Lean.ofReduceBool`,
   `Lean.trustCompiler`, or a hand-declared axiom -- means the proof is
   not unconditional, and a `grep` for `sorry` cannot detect it because
   an admitted lemma reached transitively contributes `sorryAx` without
   the token appearing in any file in the chain.
-/

open GroupApproximation
open GroupApproximation.LiteralSoficAssembly

section StatementPinning

/-- `E` is sofic, unconditionally. -/
example : IsSofic LiteralNonMFPresentation.MarkedGroup :=
  markedGroup_isSofic

/-- `E` is finitely presented, sofic, and not MF. -/
example :
    Group.IsFinitelyPresented LiteralNonMFPresentation.MarkedGroup ∧
      IsSofic LiteralNonMFPresentation.MarkedGroup ∧
      ¬ IsCDEOperatorMF LiteralNonMFPresentation.MarkedGroup :=
  markedGroup_finitelyPresented_sofic_nonMF

/-- `E` is finitely presented, hyperlinear, and not MF. -/
example :
    Group.IsFinitelyPresented LiteralNonMFPresentation.MarkedGroup ∧
      IsHyperlinear LiteralNonMFPresentation.MarkedGroup ∧
      ¬ IsCDEOperatorMF LiteralNonMFPresentation.MarkedGroup :=
  markedGroup_finitelyPresented_hyperlinear_nonMF

/-- `E` is sofic, not LEF, and not residually finite. -/
example :
    IsSofic LiteralNonMFPresentation.MarkedGroup ∧
      ¬ IsLEF LiteralNonMFPresentation.MarkedGroup ∧
      ¬ Group.ResiduallyFinite LiteralNonMFPresentation.MarkedGroup :=
  markedGroup_sofic_not_isLEF_unconditional

/-- The group really is the printed 41-relator presentation. -/
example : (LiteralNonMFPresentation.relators).card = 41 :=
  LiteralNonMFPresentation.relators_card

end StatementPinning

section AxiomClosure

#print axioms GroupApproximation.LiteralSoficAssembly.markedGroup_isSofic
#print axioms GroupApproximation.LiteralSoficAssembly.markedGroup_finitelyPresented_sofic_nonMF
#print axioms GroupApproximation.LiteralSoficAssembly.markedGroup_finitelyPresented_hyperlinear_nonMF
#print axioms GroupApproximation.LiteralSoficAssembly.markedGroup_sofic_not_isLEF_unconditional
#print axioms GroupApproximation.LiteralSoficAssembly.markedGroup_isHyperlinear
#print axioms GroupApproximation.LiteralNonMFPresentation.relators_card

end AxiomClosure
