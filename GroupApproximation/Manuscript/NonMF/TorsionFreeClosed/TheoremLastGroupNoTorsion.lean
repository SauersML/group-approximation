import GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.TheoremOfGreendlinger
import GroupApproximation.Meta.AxiomGuard

/-!
# "The last group has none"

`non_mf_groups_exist.tex`, tex 292–293 (Introduction, just before `thm:torsion-free`):

> Every example above has torsion, and in the lamp construction the obstruction is itself a
> torsion element.  The last group has none.

"The last group" is the group `Q` of `thm:torsion-free` (tex 297); the sentence asserts that
it is torsion-free.  The statement below names `Q` by the clauses of `thm:torsion-free` that
identify it as a finitely presented group all of whose homomorphisms to MF groups are trivial,
and records that it has no nontrivial element of finite order (`IsPowerTorsionFree`).

## Route

Lane nm-torsionfree-04.  `lastGroupHasNoTorsion_of_printedTorsionFreeTheorem` is an
unconditional projection out of `TorsionFreePrinted.PrintedTorsionFreeTheorem`; the endpoint
applies it to `manuscriptSentence_torsionFreeTheorem_of_greendlinger`, so its only binder is
the least-area Greendlinger leaf.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeClosed

/-- **"The last group has none"** (tex 293): the group of `thm:torsion-free` — finitely
presented, with every homomorphism to an MF group trivial — is torsion-free. -/
def LastGroupHasNoTorsion : Prop :=
  ∃ (Q : Type) (_ : Group Q),
    Group.IsFinitelyPresented Q ∧ IsPowerTorsionFree Q ∧
      (∀ (M : Type) (_ : Group M), IsOperatorMF M →
        ∀ (f : Q →* M) (x : Q), f x = 1)

/-- `thm:torsion-free` gives "the last group has none", by projecting the torsion-free clause. -/
theorem lastGroupHasNoTorsion_of_printedTorsionFreeTheorem
    (h : TorsionFreePrinted.PrintedTorsionFreeTheorem) : LastGroupHasNoTorsion := by
  obtain ⟨Q, instQ, -, hfp, htf, -, -, hkill, -⟩ := h
  exact ⟨Q, instQ, hfp, htf, hkill⟩

#audit_axioms
  GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.lastGroupHasNoTorsion_of_printedTorsionFreeTheorem

/-- **"The last group has none"** (tex 293), from the least-area Greendlinger leaf. -/
theorem manuscriptSentence_lastGroupHasNoTorsion_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    LastGroupHasNoTorsion :=
  lastGroupHasNoTorsion_of_printedTorsionFreeTheorem
    (manuscriptSentence_torsionFreeTheorem_of_greendlinger hgreendlinger)

#audit_axioms
  GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_lastGroupHasNoTorsion_of_greendlinger

end TorsionFreeClosed
end NonMF
end Manuscript
end GroupApproximation
