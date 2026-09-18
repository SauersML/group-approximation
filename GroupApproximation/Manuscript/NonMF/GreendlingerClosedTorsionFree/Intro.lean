import GroupApproximation.Manuscript.NonMF.IntroCarto07AbstractGreendlinger
import GroupApproximation.Meta.AxiomGuard

/-!
# The abstract (tex 66) and "The last group has none" (tex 292) over the Greendlinger leaf

Lane gl-assembly-07.  `non_mf_groups_exist.tex`, line 66 (abstract):

> We also construct a sofic group that is not MF, whose canonical trace on the maximal group
> $C^*$-algebra is amenable but not quasidiagonal, and a finitely presented torsion-free group
> with property~(T) and no nontrivial homomorphism to an MF group.

and line 292:

> Every example above has torsion, and in the lamp construction the obstruction is itself a
> torsion element.  The last group has none.

## Route

`IntroCarto07.manuscriptSentence_abstractSecondSentence_of_greendlinger` and
`IntroCarto07.manuscriptSentence_lastGroupHasNone_of_greendlinger` feed
`TorsionFreeGreendlingerLeaf.printedTorsionFreeTheorem_of_greendlinger` into the printed
`thm:torsion-free` assembly.  The sofic, amenable-but-not-quasidiagonal half of tex 66 is closed
(`IntroAmenable.manuscriptSentence_soficNonMFAmenableNonQDTrace`).  The torsion-free clause of
tex 292 is the clause `IsPowerTorsionFree Q` of `TorsionFreePrinted.PrintedTorsionFreeTheorem`,
through `IsPowerTorsionFree.not_isOfFinOrder`.

`IntroCarriersStatement` bundles the two sentences.  Once gl-assembly-04 lands, the closed
endpoint is `introCarriers_of_greendlinger` applied to
`AsmClose.relativeGreendlingerQuasiGeodesicLeastAreaClosed.{0,0,0}`.

## Manuscript status

Partial on `hgreendlinger` only.
-/

namespace GroupApproximation.Manuscript.NonMF.GreendlingerClosedTorsionFree

open GroupApproximation.Manuscript.NonMF.TorsionFree

/-- **tex 66 (whole sentence) and tex 292 as one proposition.**  The first conjunct is the abstract
sentence: a countable sofic non-MF group whose canonical maximal trace is amenable but not
quasidiagonal, and an infinite finitely presented torsion-free group with property (T) and no
nontrivial homomorphism to an MF group.  The second is "The last group has none": the group of
`thm:torsion-free` is infinite, every nontrivial element is killed by every homomorphism to an MF
group, and no nontrivial element has finite order. -/
def IntroCarriersStatement : Prop :=
  ((∃ (W : Type) (_ : Group W) (_ : Countable W),
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
        ∀ (M : Type) [Group M], IsOperatorMF M → ∀ f : Q →* M, f = 1)) ∧
  (∃ (Q : Type) (_ : Group Q),
      IsTwoGenerated Q ∧ Group.IsFinitelyPresented Q ∧ IsAcylindricallyHyperbolic Q ∧
        HasKazhdanPropertyT.{0, 0} Q ∧ Infinite Q ∧
        ∀ g : Q, g ≠ 1 →
          (∀ (M : Type) [Group M], IsOperatorMF M → ∀ f : Q →* M, f g = 1) ∧
            ¬ IsOfFinOrder g)

/-- **tex 66 and tex 292 over the least-area Greendlinger leaf.** -/
theorem introCarriers_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    IntroCarriersStatement :=
  ⟨IntroCarto07.manuscriptSentence_abstractSecondSentence_of_greendlinger hgreendlinger,
    IntroCarto07.manuscriptSentence_lastGroupHasNone_of_greendlinger hgreendlinger⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedTorsionFree.introCarriers_of_greendlinger

/-- **tex 66, the whole abstract sentence** (census row a16637da7249), over the leaf. -/
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
  (introCarriers_of_greendlinger hgreendlinger).1

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedTorsionFree.manuscriptSentence_abstractSecondSentence_of_greendlinger

/-- **tex 292, "The last group has none"** (census row abb56744db26), over the leaf. -/
theorem manuscriptSentence_lastGroupHasNone_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    ∃ (Q : Type) (_ : Group Q),
      IsTwoGenerated Q ∧ Group.IsFinitelyPresented Q ∧ IsAcylindricallyHyperbolic Q ∧
        HasKazhdanPropertyT.{0, 0} Q ∧ Infinite Q ∧
        ∀ g : Q, g ≠ 1 →
          (∀ (M : Type) [Group M], IsOperatorMF M → ∀ f : Q →* M, f g = 1) ∧
            ¬ IsOfFinOrder g :=
  (introCarriers_of_greendlinger hgreendlinger).2

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedTorsionFree.manuscriptSentence_lastGroupHasNone_of_greendlinger

end GroupApproximation.Manuscript.NonMF.GreendlingerClosedTorsionFree
