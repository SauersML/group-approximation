import GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.TheoremOfGreendlinger
import GroupApproximation.Manuscript.NonMF.TorsionFreeJoint.EndpointStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# "Its reduced C⋆-algebra is simple ... and is not MF", for the `Q` of `thm:torsion-free`

`non_mf_groups_exist.tex`, tex 303–305 (Introduction, after `thm:torsion-free`):

> Section `sec:torsion-free` builds `Q` from Fournier-Facio's torsion-free property-(T) group
> and Hull's small cancellation theorem.  Its reduced C⋆-algebra is simple, has a unique
> tracial state and stable rank one, and is not MF.

"Its" refers to the group `Q` of `thm:torsion-free` (tex 297).  `IntroReducedAlgebraNotMF`
states the seven clauses of `thm:torsion-free` (copied from
`TorsionFreePrinted.PrintedTorsionFreeTheorem`) and the four C⋆ clauses of the sentence, with
one existential `Q`, so the algebra sentence is about the group of the theorem and not about
a separately quantified group.

## Route

Lane nm-torsionfree-07.
* `introReducedAlgebraNotMF_of_printedTorsionFreeTheorem` (unconditional): take `Q` from
  `PrintedTorsionFreeTheorem` and apply
  `TorsionFreeCStar.manuscriptSentence_reducedAlgebraSimpleUniqueTraceStableRankNotMF`, which
  needs exactly the finitely presented, torsion-free, acylindrically hyperbolic and
  "homomorphisms to MF groups are trivial" clauses.
* `introReducedAlgebraNotMF_of_joint` (unconditional): the same sentence as a weakening of
  lane nm-torsionfree-06's joint predicate
  `TorsionFreeJoint.PrintedTorsionFreeTheoremWithRegularAlgebra`.
* `manuscriptSentence_introReducedAlgebraNotMF_of_greendlinger`: the first reduction applied
  to `manuscriptSentence_torsionFreeTheorem_of_greendlinger`, so its only binder is the
  least-area Greendlinger leaf `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeClosed

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted
open GroupApproximation.ReducedGroupCStarTrace

/-- **"Its reduced C⋆-algebra is simple, has a unique tracial state and stable rank one, and is
not MF"** (tex 303), for the group `Q` of `thm:torsion-free`: the seven clauses of the theorem,
then the four clauses of the sentence for `C*_r(Q)`. -/
def IntroReducedAlgebraNotMF : Prop :=
  ∃ (Q : Type) (_ : Group Q),
    IsTwoGenerated Q ∧ Group.IsFinitelyPresented Q ∧ IsPowerTorsionFree Q ∧
    IsAcylindricallyHyperbolic Q ∧ HasKazhdanPropertyT.{0, 0} Q ∧
    (∀ (M : Type) (_ : Group M), IsOperatorMF M →
      ∀ (f : Q →* M) (x : Q), f x = 1) ∧
    (∀ (L : Type) (_ : Group L) (r : Q →* L), Function.Surjective r →
      Nontrivial L → ¬ IsOperatorMF L) ∧
    IsSimpleCStar (ReducedGroupCStar Q) ∧
    HasUniqueTracialState (ReducedGroupCStar Q) ∧
    IsStableRankOne (ReducedGroupCStar Q) ∧
    ¬ IsMFAlgebra (ReducedGroupCStar Q)

/-- `thm:torsion-free` gives the introduction's C⋆ sentence for the same `Q`. -/
theorem introReducedAlgebraNotMF_of_printedTorsionFreeTheorem
    (h : PrintedTorsionFreeTheorem) : IntroReducedAlgebraNotMF := by
  obtain ⟨Q, instQ, hgen, hfp, htf, hacyl, hT, hkill, hquot⟩ := h
  letI := instQ
  haveI := hfp
  haveI := hacyl
  obtain ⟨hsimple, huniq, hsr, hnotMF⟩ :=
    TorsionFreeCStar.manuscriptSentence_reducedAlgebraSimpleUniqueTraceStableRankNotMF
      Q htf hkill
  exact ⟨Q, instQ, hgen, hfp, htf, hacyl, hT, hkill, hquot, hsimple, huniq, hsr, hnotMF⟩

#audit_axioms
  GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.introReducedAlgebraNotMF_of_printedTorsionFreeTheorem

/-- The introduction's C⋆ sentence is a weakening of the joint predicate of
`thm:torsion-free` and `cor:regular-nonmf-algebra` (lane nm-torsionfree-06). -/
theorem introReducedAlgebraNotMF_of_joint
    (h : TorsionFreeJoint.PrintedTorsionFreeTheoremWithRegularAlgebra) :
    IntroReducedAlgebraNotMF := by
  obtain ⟨Q, instQ, g₁, g₂, hcl, hfp, htf, hacyl, hT, hkill, hquot, -, -, -, -, -,
    hsimple, huniq, hsr, -, hnotMF⟩ := h
  exact ⟨Q, instQ, ⟨g₁, g₂, hcl⟩, hfp, htf, hacyl, hT, hkill, hquot, hsimple, huniq, hsr,
    hnotMF⟩

#audit_axioms
  GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.introReducedAlgebraNotMF_of_joint

/-- **"Its reduced C⋆-algebra is simple, has a unique tracial state and stable rank one, and is
not MF"** (tex 303), for the `Q` of `thm:torsion-free`, from the least-area Greendlinger
leaf. -/
theorem manuscriptSentence_introReducedAlgebraNotMF_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    IntroReducedAlgebraNotMF :=
  introReducedAlgebraNotMF_of_printedTorsionFreeTheorem
    (manuscriptSentence_torsionFreeTheorem_of_greendlinger hgreendlinger)

#audit_axioms
  GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_introReducedAlgebraNotMF_of_greendlinger

end TorsionFreeClosed
end NonMF
end Manuscript
end GroupApproximation
