import GroupApproximation.Manuscript.NonMF.TorsionFreePrintedTheorem
import GroupApproximation.Manuscript.NonMF.RegularNonMFAlgebra
import GroupApproximation.Meta.AxiomGuard

/-!
# The torsion-free clause of the abstract, and "The last group has none"

`non_mf_groups_exist.tex`, line 66 (abstract), second half:

> We also construct ... a finitely presented torsion-free group with property~(T) and no
> nontrivial homomorphism to an MF group.

`non_mf_groups_exist.tex`, lines 290-292 (Introduction, before `thm:torsion-free`):

> Every example above has torsion, and in the lamp construction the obstruction is itself a
> torsion element.  The last group has none.

## Scope: conditional on `thm:torsion-free`

Both endpoints here are **assembly over the printed theorem**
`TorsionFreePrinted.PrintedTorsionFreeTheorem` (TorsionFreePrintedTheorem.lean:249), taken
as the hypothesis `hthm`.  They are *not* unconditional results.  The closed forms at the
single open waist `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement` are in
`IntroCarto07AbstractGreendlinger`; the census rows stay `partial` until that waist closes.

## Proof route

Unpack the seven printed clauses of `PrintedTorsionFreeTheorem`.

* "finitely presented" and "property (T)" are clauses of the theorem.
* "torsion-free": the clause `IsPowerTorsionFree Q` gives `¬ IsOfFinOrder g` for `g ≠ 1`
  (`IsPowerTorsionFree.not_isOfFinOrder`).
* "no nontrivial homomorphism to an MF group": the killing clause gives `f x = 1` for every
  `x`, so `f = 1` by `MonoidHom.ext`.
* The group is infinite (so the killing clause is not vacuous), because it is acylindrically
  hyperbolic (`TorsionFreePrinted.infinite_of_acylHyperbolic`).
* "The last group has none": `Q` has no nontrivial torsion element, while every element of `Q`
  lies in the obstruction (is killed by every homomorphism to an MF group).
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace IntroCarto07

open GroupApproximation.Manuscript.NonMF.TorsionFree

/-- **tex 66, second half, over `thm:torsion-free`.**  There is an infinite finitely presented
torsion-free group with property (T) and no nontrivial homomorphism to an MF group.

Conditional on `TorsionFreePrinted.PrintedTorsionFreeTheorem`; not an unconditional result. -/
theorem manuscriptSentence_abstractTorsionFreeGroup_of_printedTorsionFreeTheorem
    (hthm : TorsionFreePrinted.PrintedTorsionFreeTheorem) :
    ∃ (Q : Type) (_ : Group Q),
      Group.IsFinitelyPresented Q ∧ Infinite Q ∧ (∀ g : Q, IsOfFinOrder g → g = 1) ∧
        HasKazhdanPropertyT.{0, 0} Q ∧
        ∀ (M : Type) [Group M], IsOperatorMF M → ∀ f : Q →* M, f = 1 := by
  obtain ⟨Q, instQ, -, hfp, htf, hacyl, hT, hkill, -⟩ := hthm
  letI := instQ
  haveI := hacyl
  refine ⟨Q, instQ, hfp, TorsionFreePrinted.infinite_of_acylHyperbolic Q, ?_, hT, ?_⟩
  · intro g hg
    by_contra hne
    exact IsPowerTorsionFree.not_isOfFinOrder htf hne hg
  · intro M _ hM f
    exact MonoidHom.ext fun x => (hkill M _ hM f x).trans (MonoidHom.one_apply x).symm

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto07.manuscriptSentence_abstractTorsionFreeGroup_of_printedTorsionFreeTheorem

/-- **tex 292, "The last group has none", over `thm:torsion-free`.**

The group `Q` of `thm:torsion-free` (two-generated, finitely presented, acylindrically
hyperbolic, property (T), every homomorphism to an MF group trivial) is infinite, and it has no
torsion: every nontrivial element of `Q` lies in the obstruction (it is killed by every
homomorphism to an MF group) and has infinite order.  This is the contrast with the lamp
construction, where the obstruction is a torsion element.

Conditional on `TorsionFreePrinted.PrintedTorsionFreeTheorem`; not an unconditional result. -/
theorem manuscriptSentence_lastGroupHasNone_of_printedTorsionFreeTheorem
    (hthm : TorsionFreePrinted.PrintedTorsionFreeTheorem) :
    ∃ (Q : Type) (_ : Group Q),
      IsTwoGenerated Q ∧ Group.IsFinitelyPresented Q ∧ IsAcylindricallyHyperbolic Q ∧
        HasKazhdanPropertyT.{0, 0} Q ∧ Infinite Q ∧
        ∀ g : Q, g ≠ 1 →
          (∀ (M : Type) [Group M], IsOperatorMF M → ∀ f : Q →* M, f g = 1) ∧
            ¬ IsOfFinOrder g := by
  obtain ⟨Q, instQ, hgen, hfp, htf, hacyl, hT, hkill, -⟩ := hthm
  letI := instQ
  haveI := hacyl
  refine ⟨Q, instQ, hgen, hfp, hacyl, hT,
    TorsionFreePrinted.infinite_of_acylHyperbolic Q, ?_⟩
  intro g hg
  refine ⟨?_, IsPowerTorsionFree.not_isOfFinOrder htf hg⟩
  intro M _ hM f
  exact hkill M _ hM f g

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto07.manuscriptSentence_lastGroupHasNone_of_printedTorsionFreeTheorem

end IntroCarto07
end NonMF
end Manuscript
end GroupApproximation
