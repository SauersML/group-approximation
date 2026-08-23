import GroupApproximation.Sofic.LiteralNonMFEndpoint
import GroupApproximation.Sofic.LiteralSoficConsequences

/-!
# Theorem A in one declaration

Everything the manuscript advertises about the literal group `E` is already
proved, but it is proved in pieces, and the pieces live in different modules:

* the alphabet and the relator count are in
  `LiteralNonMFPresentation.manuscriptLiteralPresentation`;
* soficity and hyperlinearity are in `LiteralSoficAssembly`;
* the central involution, the corona annihilation and the three failures of MF
  are in `LiteralNonMFEndpoint.manuscriptTheoremA`.

A reader following a badge lands on one of the three and has to reassemble the
other two by hand.  Worse, the three are about *different-looking* objects --
a presentation, a group, a `C*`-algebra -- so the reassembly is exactly the
step at which a reader can wonder whether the same `E` is meant throughout.

`manuscriptTheoremA_package` is the reassembly, done once.  Every conjunct is
a citation of an existing theorem; nothing new is proved here, and the module
deliberately contains a single declaration so that the badge attached to it
cannot drift away from the statement it certifies.

The one thing the package does add is the *identification*: all six groups of
clauses are about the same term `MarkedGroup`, and the marked element is the
same term `mark = wordInMarkedGroup markedWord` in all of them.  That is what
a reader has to take on faith when the clauses are spread over three files.
-/

namespace GroupApproximation
namespace LiteralTheoremAPackage

open LiteralNonMFPresentation ReducedGroupCStarTrace

/-- **Theorem A, whole.**

The literal group `E` of the manuscript, in one statement:

1. *the object* -- eight generators, forty-one relators, `E` is the presented
   quotient by exactly those relators, and it is finitely presented;
2. *what it approximates* -- `E` is sofic, hence hyperlinear;
3. *the mark* -- the printed word `w` is a nontrivial central involution;
4. *corona annihilation* -- every homomorphism of `E` into every
   unitary-sequence corona in natural matrix dimensions kills `w`;
5. *the failures* -- `E` is not operator MF under the genuine-corona
   convention nor under the plain one, and neither its maximal nor its reduced
   group `C*`-algebra is MF.

Clauses 3-5 are `LiteralNonMFEndpoint.manuscriptTheoremA` together with
`literal_not_isOperatorMF`; clause 1 is
`LiteralNonMFPresentation.manuscriptLiteralPresentation`; clause 2 is
`LiteralSoficAssembly`.  Their conjunction is the printed theorem. -/
theorem manuscriptTheoremA_package :
    (Fintype.card Generator = 8 ∧
        relators.card = 41 ∧
        MarkedGroup = PresentedGroup
          ((relators : Finset (FreeGroup Generator)) :
            Set (FreeGroup Generator)) ∧
        Group.IsFinitelyPresented MarkedGroup) ∧
      (IsSofic MarkedGroup ∧ IsHyperlinear MarkedGroup) ∧
      (mark = wordInMarkedGroup markedWord ∧ mark ≠ 1 ∧ mark ^ 2 = 1 ∧
        ∀ g : MarkedGroup, Commute mark g) ∧
      (∀ d : ℕ → ℕ, (∀ n, 0 < d n) →
        ∀ Theta : MarkedGroup →*
          NormMatrixCoronaUnitary (fun n ↦ naturalFiniteModel (d n)),
          Theta mark = 1) ∧
      ¬ IsCDEOperatorMF MarkedGroup ∧
      ¬ IsOperatorMF MarkedGroup ∧
      ¬ IsMFAlgebra (MaximalGroupCStar MarkedGroup) ∧
      ¬ IsMFAlgebra (ReducedGroupCStar MarkedGroup) := by
  obtain ⟨⟨hne, hsq, hcentral⟩, hcorona, hcde, hmax, hred⟩ :=
    LiteralNonMFEndpoint.manuscriptTheoremA
  exact ⟨⟨generator_card, relators_card, rfl, inferInstance⟩,
    ⟨LiteralSoficAssembly.markedGroup_isSofic,
      LiteralSoficAssembly.markedGroup_isHyperlinear⟩,
    ⟨rfl, hne, hsq, hcentral⟩,
    hcorona, hcde, LiteralNonMFEndpoint.literal_not_isOperatorMF, hmax, hred⟩

end LiteralTheoremAPackage
end GroupApproximation
