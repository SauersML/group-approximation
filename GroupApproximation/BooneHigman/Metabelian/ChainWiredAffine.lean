import GroupApproximation.BooneHigman.Metabelian.ChainHost
import GroupApproximation.BooneHigman.Metabelian.AffineFPMain
import GroupApproximation.Meta.AxiomGuard

/-!
# Chain wiring, part 1: the affine extension leaf (lane `bh-met-27`)

The chain skeleton (`ChainHost`) states the leaf `AffineExtensionFPStatement`: for a finitely
generated commutative ring `R` and `n ≥ 4`, if `E_n(R)` is finitely presented then so is
`R^n ⋊ E_n(R)`, with the action `affineAction n R`.  Lane `bh-met-05` (`AffineFPMain`) proved
`AffineFP.isFinitelyPresented_affine_fin` for `AffineFP.AffineElementary (Fin n) R`, the semidirect
product for the action `AffineFP.affAction (Fin n) R`.

The two actions are equal: both send `g ∈ E_n(R)` to `v ↦ g *ᵥ v`.  In `ChainHost` this goes
through `DistribMulAction.toAddAut` and `MulAutMultiplicative`, where
`g • v = (g : M) • v = g *ᵥ v` (`Units.smul_def`, `Matrix.smul_eq_mulVec`, both `rfl`); in
`AffineFPModel` it is `vecEquiv`.
So the two semidirect products are the same type, and the leaf follows (`subst`).

* `affineAction_eq_affAction`: the two actions agree.
* `isFinitelyPresented_semidirectProduct_of_eq`: transport of finite presentability along an
  equality of actions.
* `affineExtensionFPStatement_holds`: **the leaf `AffineExtensionFPStatement`, unconditionally.**
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Chain

/-- The chain-skeleton action `affineAction n R` is the action `AffineFP.affAction (Fin n) R` of
lane `bh-met-05`: both are `g ↦ (v ↦ g *ᵥ v)`. -/
theorem affineAction_eq_affAction (n : ℕ) (R : Type) [CommRing R] :
    affineAction n R = AffineFP.affAction (Fin n) R :=
  MonoidHom.ext fun _ => MulEquiv.ext fun _ => rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.affineAction_eq_affAction

/-- Finite presentability of `N ⋊[φ] G` only depends on `φ` up to equality. -/
theorem isFinitelyPresented_semidirectProduct_of_eq {N G : Type} [Group N] [Group G]
    {φ ψ : G →* MulAut N} (h : φ = ψ)
    (hφ : Group.IsFinitelyPresented (SemidirectProduct N G φ)) :
    Group.IsFinitelyPresented (SemidirectProduct N G ψ) := by
  subst h
  exact hφ

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Chain.isFinitelyPresented_semidirectProduct_of_eq

/-- **The affine extension leaf holds**: for a finitely generated commutative ring `R` and
`n ≥ 4`, if `E_n(R)` is finitely presented then so is `R^n ⋊ E_n(R)`.  This is
`AffineFP.isFinitelyPresented_affine_fin` (lane `bh-met-05`) with the action identified by
`affineAction_eq_affAction`. -/
theorem affineExtensionFPStatement_holds : AffineExtensionFPStatement := by
  intro R _ hR n hn hE
  haveI : Algebra.FiniteType ℤ R := hR
  exact isFinitelyPresented_semidirectProduct_of_eq (affineAction_eq_affAction n R).symm
    (AffineFP.isFinitelyPresented_affine_fin n hn R hE)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.affineExtensionFPStatement_holds

end Chain
end Metabelian
end BooneHigman
end GroupApproximation
