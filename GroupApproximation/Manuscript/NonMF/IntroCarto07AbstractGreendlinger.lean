import GroupApproximation.Manuscript.NonMF.IntroCarto07AbstractSentence
import GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf
import GroupApproximation.Meta.AxiomGuard

/-!
# tex 66 and tex 292 at the Greendlinger waist

`non_mf_groups_exist.tex`, line 66 (abstract):

> We also construct a sofic group that is not MF, whose canonical trace on the maximal group
> $C^*$-algebra is amenable but not quasidiagonal, and a finitely presented torsion-free group
> with property~(T) and no nontrivial homomorphism to an MF group.

`non_mf_groups_exist.tex`, line 292:

> The last group has none.

## Scope: conditional on the open waist G1

The endpoints of `IntroCarto07AbstractTorsionFree` and `IntroCarto07AbstractSentence` take
`thm:torsion-free` (`TorsionFreePrinted.PrintedTorsionFreeTheorem`) as a hypothesis.  This
module feeds them `TorsionFreeGreendlingerLeaf.printedTorsionFreeTheorem_of_greendlinger`
(TorsionFreeGreendlingerLeaf.lean:149), which proves that theorem over exactly one open
statement, `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}`
(Osin's Lemma 4.4 at least-area diagrams, GGT/VanKampen/Estimating/OsinAppendixSections.lean:122),
owned by the gl-* lanes.  These endpoints are therefore **not** unconditional; the census rows
stay `partial` until that statement is proved.  Nothing is added mathematically here: the
module is assembly only, and it lives in its own file so that a moving carrier name affects
only this file.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace IntroCarto07

open GroupApproximation.Manuscript.NonMF.TorsionFree

/-- **tex 66, second half, over the Greendlinger waist.**  Conditional on
`GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}`. -/
theorem manuscriptSentence_abstractTorsionFreeGroup_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    ∃ (Q : Type) (_ : Group Q),
      Group.IsFinitelyPresented Q ∧ Infinite Q ∧ (∀ g : Q, IsOfFinOrder g → g = 1) ∧
        HasKazhdanPropertyT.{0, 0} Q ∧
        ∀ (M : Type) [Group M], IsOperatorMF M → ∀ f : Q →* M, f = 1 :=
  manuscriptSentence_abstractTorsionFreeGroup_of_printedTorsionFreeTheorem
    (TorsionFreeGreendlingerLeaf.printedTorsionFreeTheorem_of_greendlinger hgreendlinger)

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto07.manuscriptSentence_abstractTorsionFreeGroup_of_greendlinger

/-- **tex 292, "The last group has none", over the Greendlinger waist.**  Conditional on
`GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}`. -/
theorem manuscriptSentence_lastGroupHasNone_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    ∃ (Q : Type) (_ : Group Q),
      IsTwoGenerated Q ∧ Group.IsFinitelyPresented Q ∧ IsAcylindricallyHyperbolic Q ∧
        HasKazhdanPropertyT.{0, 0} Q ∧ Infinite Q ∧
        ∀ g : Q, g ≠ 1 →
          (∀ (M : Type) [Group M], IsOperatorMF M → ∀ f : Q →* M, f g = 1) ∧
            ¬ IsOfFinOrder g :=
  manuscriptSentence_lastGroupHasNone_of_printedTorsionFreeTheorem
    (TorsionFreeGreendlingerLeaf.printedTorsionFreeTheorem_of_greendlinger hgreendlinger)

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto07.manuscriptSentence_lastGroupHasNone_of_greendlinger

/-- **tex 66, the whole sentence, over the Greendlinger waist.**  The first half is closed; the
second half is conditional on
`GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}`. -/
theorem manuscriptSentence_abstractSecondSentence_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    (∃ (W : Type) (_ : Group W) (_ : Countable W),
      GroupApproximation.IsSofic W ∧ ¬ IntroAmenable.LiteralMF W ∧
        ¬ GroupApproximation.IsOperatorMF W ∧
        GroupApproximation.Quasidiagonal.IsAmenableTrace
          (fun a : GroupApproximation.MaximalGroupCStar W ↦
            GroupApproximation.canonicalMaximalTrace W a) ∧
        ¬ GroupApproximation.Quasidiagonal.IsQuasidiagonalTrace
          (fun a : GroupApproximation.MaximalGroupCStar W ↦
            GroupApproximation.canonicalMaximalTrace W a)) ∧
    (∃ (Q : Type) (_ : Group Q),
      Group.IsFinitelyPresented Q ∧ Infinite Q ∧ (∀ g : Q, IsOfFinOrder g → g = 1) ∧
        HasKazhdanPropertyT.{0, 0} Q ∧
        ∀ (M : Type) [Group M], IsOperatorMF M → ∀ f : Q →* M, f = 1) :=
  manuscriptSentence_abstractSecondSentence_of_printedTorsionFreeTheorem
    (TorsionFreeGreendlingerLeaf.printedTorsionFreeTheorem_of_greendlinger hgreendlinger)

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto07.manuscriptSentence_abstractSecondSentence_of_greendlinger

end IntroCarto07
end NonMF
end Manuscript
end GroupApproximation
