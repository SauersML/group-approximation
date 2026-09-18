import GroupApproximation.Manuscript.NonMF.GreendlingerClosedTorsionFree.Theorem
import GroupApproximation.Manuscript.NonMF.TorsionFreePrintedTheorem
import GroupApproximation.Manuscript.NonMF.TorsionFreeCStar.RegularAlgebra
import GroupApproximation.Meta.AxiomGuard

/-!
# "Its reduced C*-algebra is simple ..." (tex 303) for the group of `thm:torsion-free`

Lane gl-assembly-07.  `non_mf_groups_exist.tex`, lines 303–306:

> Section~\ref{sec:torsion-free} builds $Q$ from Fournier-Facio's torsion-free property-(T)
> group and Hull's small cancellation theorem.  Its reduced $C^*$-algebra is simple, has a unique
> tracial state and stable rank one, and is not MF.

## Route

`PrintedTorsionFreeGroupAlgebra` ties the four algebra clauses to the *same* group `Q` as the seven
clauses of `thm:torsion-free`.  `torsionFreeGroupAlgebra_of_printedTorsionFreeTheorem` unpacks
`TorsionFreePrinted.PrintedTorsionFreeTheorem` and applies the closed
`TorsionFreeCStar.manuscriptSentence_reducedAlgebraSimpleUniqueTraceStableRankNotMF`
(TorsionFreeCStar/RegularAlgebra.lean:89), which uses only the finitely presented, torsion-free,
acylindrically hyperbolic and MF-killing clauses.  Composing with
`manuscriptSentence_torsionFreeTheorem_of_greendlinger` gives the sentence over the leaf.

## Manuscript status

Partial on `hgreendlinger` only.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace GreendlingerClosedTorsionFree

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted
open GroupApproximation.ReducedGroupCStarTrace

/-- **tex 303, for the group of `thm:torsion-free`.**  There is a group `Q` satisfying the seven
printed clauses of `thm:torsion-free` whose reduced C*-algebra is simple, has a unique tracial
state and stable rank one, and is not MF. -/
def PrintedTorsionFreeGroupAlgebra : Prop :=
  ∃ (Q : Type) (_ : Group Q),
    IsTwoGenerated Q ∧ Group.IsFinitelyPresented Q ∧ IsPowerTorsionFree Q ∧
      IsAcylindricallyHyperbolic Q ∧ HasKazhdanPropertyT.{0, 0} Q ∧
        (∀ (M : Type) (_ : Group M), IsOperatorMF M →
          ∀ (f : Q →* M) (x : Q), f x = 1) ∧
        (∀ (L : Type) (_ : Group L) (r : Q →* L), Function.Surjective r →
          Nontrivial L → ¬ IsOperatorMF L) ∧
        (IsSimpleCStar (ReducedGroupCStar Q) ∧
          HasUniqueTracialState (ReducedGroupCStar Q) ∧
            IsStableRankOne (ReducedGroupCStar Q) ∧
              ¬ IsMFAlgebra (ReducedGroupCStar Q))

/-- **tex 303 from `thm:torsion-free`**: the algebra clauses hold for the group of the printed
theorem, by the closed `TorsionFreeCStar.manuscriptSentence_reducedAlgebraSimpleUniqueTraceStableRankNotMF`. -/
theorem torsionFreeGroupAlgebra_of_printedTorsionFreeTheorem
    (hthm : PrintedTorsionFreeTheorem) : PrintedTorsionFreeGroupAlgebra := by
  obtain ⟨Q, instQ, hgen, hfp, htf, hacyl, hT, hkill, hquot⟩ := hthm
  letI := instQ
  haveI := hfp
  haveI := hacyl
  exact ⟨Q, instQ, hgen, hfp, htf, hacyl, hT, hkill, hquot,
    TorsionFreeCStar.manuscriptSentence_reducedAlgebraSimpleUniqueTraceStableRankNotMF Q htf hkill⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedTorsionFree.torsionFreeGroupAlgebra_of_printedTorsionFreeTheorem

/-- **tex 303, over the least-area Greendlinger leaf** (census row dce7a9ff4e83). -/
theorem manuscriptSentence_torsionFreeGroupAlgebra_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    PrintedTorsionFreeGroupAlgebra :=
  torsionFreeGroupAlgebra_of_printedTorsionFreeTheorem
    (manuscriptSentence_torsionFreeTheorem_of_greendlinger hgreendlinger)

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedTorsionFree.manuscriptSentence_torsionFreeGroupAlgebra_of_greendlinger

end GreendlingerClosedTorsionFree
end NonMF
end Manuscript
end GroupApproximation
