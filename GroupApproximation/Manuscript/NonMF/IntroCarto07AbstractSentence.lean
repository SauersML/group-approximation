import GroupApproximation.Manuscript.NonMF.IntroCarto07AbstractTorsionFree
import GroupApproximation.Manuscript.NonMF.IntroAmenable.SoficNonMF
import GroupApproximation.Meta.AxiomGuard

/-!
# The abstract sentence at tex 66, both halves

`non_mf_groups_exist.tex`, line 66 (abstract):

> We also construct a sofic group that is not MF, whose canonical trace on the maximal group
> $C^*$-algebra is amenable but not quasidiagonal, and a finitely presented torsion-free group
> with property~(T) and no nontrivial homomorphism to an MF group.

## Scope: the second half is conditional on `thm:torsion-free`

* First half (sofic, not MF, amenable non-quasidiagonal canonical maximal trace): closed,
  `IntroAmenable.manuscriptSentence_soficNonMFAmenableNonQDTrace`, over the closed
  `AmenableTraceTheorem.manuscriptAmenableNonquasidiagonalTraceCore`.
* Second half: `IntroCarto07.manuscriptSentence_abstractTorsionFreeGroup_of_printedTorsionFreeTheorem`,
  over the hypothesis `hthm : TorsionFreePrinted.PrintedTorsionFreeTheorem`.

So the endpoint below is **not** an unconditional result.  The form at the single open waist
`GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement` is in
`IntroCarto07AbstractGreendlinger`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace IntroCarto07

/-- **tex 66, the whole sentence, over `thm:torsion-free`.**  There is a countable sofic group
that is not MF (for the Introduction's printed definition `LiteralMF` and for `IsOperatorMF`)
whose canonical trace on the maximal group `C*`-algebra is amenable but not quasidiagonal, and
there is an infinite finitely presented torsion-free group with property (T) and no nontrivial
homomorphism to an MF group.

Conditional on `TorsionFreePrinted.PrintedTorsionFreeTheorem`; not an unconditional result. -/
theorem manuscriptSentence_abstractSecondSentence_of_printedTorsionFreeTheorem
    (hthm : TorsionFreePrinted.PrintedTorsionFreeTheorem) :
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
  ⟨IntroAmenable.manuscriptSentence_soficNonMFAmenableNonQDTrace,
    manuscriptSentence_abstractTorsionFreeGroup_of_printedTorsionFreeTheorem hthm⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto07.manuscriptSentence_abstractSecondSentence_of_printedTorsionFreeTheorem

end IntroCarto07
end NonMF
end Manuscript
end GroupApproximation
