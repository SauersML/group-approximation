import GroupApproximation.Sofic.OperatorMF
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:torsion-free`, the "in particular" clause

`non_mf_groups_exist.tex`, `thm:torsion-free` (tex lines 297–300):

> There is a two-generated, finitely presented, torsion-free, acylindrically
> hyperbolic group `Q` with property (T) such that every homomorphism from `Q`
> to an MF group is trivial.  In particular, no nontrivial quotient of `Q` is
> MF.

This module proves the second sentence from the first, for an arbitrary group
`Q`: if every homomorphism from `Q` to an MF group is trivial, then no
nontrivial quotient of `Q` is MF.  The argument is the one-line one: an MF
quotient `Q ↠ L` is itself a homomorphism to an MF group, hence trivial, and a
surjective trivial homomorphism has trivial target.

"MF" is `IsOperatorMF`, the operator-norm predicate used by the printed
statement `TorsionFreePrinted.PrintedTorsionFreeTheorem`.

## Proof route

Pick `y ≠ 1` in `L`, lift it to `x ∈ Q` along the surjection, and apply the
hypothesis at the quotient map itself.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeCStar

/-- **"In particular, no nontrivial quotient of `Q` is MF."**  For any group
`Q` all of whose homomorphisms to MF groups are trivial, no nontrivial quotient
of `Q` is MF. -/
theorem manuscriptSentence_noNontrivialQuotientMF (Q : Type) [Group Q]
    (hkill : ∀ (M : Type) (_ : Group M), IsOperatorMF M →
      ∀ (f : Q →* M) (x : Q), f x = 1) :
    ∀ (L : Type) (_ : Group L) (r : Q →* L), Function.Surjective r →
      Nontrivial L → ¬ IsOperatorMF L := by
  intro L instL r hr hne hMF
  letI := instL
  haveI := hne
  obtain ⟨y, hy⟩ := exists_ne (1 : L)
  obtain ⟨x, rfl⟩ := hr y
  exact hy (hkill L instL hMF r x)

end TorsionFreeCStar
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeCStar.manuscriptSentence_noNontrivialQuotientMF
