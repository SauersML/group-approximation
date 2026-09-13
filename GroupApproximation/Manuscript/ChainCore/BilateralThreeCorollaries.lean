import GroupApproximation.Manuscript.ChainCore.BilateralThreeStatement
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional
import GroupApproximation.Meta.AxiomGuard

/-!
# `prop:bilateral-three`: the Introduction sentence and the Kazhdan core

`non_mf_groups_exist.tex`, Introduction (tex 252–255):

> Section~`sec:chain-core` identifies restriction to the chain-recurrent set as the universal
> directly finite ring quotient, and proves that `R_X` is directly finite exactly when
> `GL₃(R_X)` is MF.

The second clause is the case `n = 3` of Proposition `prop:bilateral-three`:
`printedIntroDirectlyFiniteIffGLThreeMF_of_printedBilateralThree`.

Proof of `prop:bilateral-three` (tex 1556–1558):

> It is finitely generated, so `L = EL₃(S)` has property~(T)~[EJZ, Theorem 1.1].  Embed it in
> `GL₃(R_X)` by adjoining identity on `1 - p`.

`hasKazhdanPropertyT_range_of_injective` transports the repository's unconditional
Ershov--Jaikin-Zapirain theorem `FullDefectRingEJZUnconditional.ejz` along an injective
homomorphism out of `EL₃(S)`, for a finitely generated ring `S`.  This is the property-(T)
clause of `BilateralThreeCellStatement`, once the corner embedding is supplied.
-/

namespace GroupApproximation
namespace Manuscript
namespace ChainCore
namespace BilateralThree

open GroupApproximation.Manuscript.OneSidedMFRadical

/-- **Introduction (tex 253–255), second clause:** "`R_X` is directly finite exactly when
`GL₃(R_X)` is MF", under the standing hypotheses of `sec:chain-core`. -/
def PrintedIntroDirectlyFiniteIffGLThreeMF : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [TopologicalSpace.MetrizableSpace X]
    [TotallyDisconnectedSpace X] [Nonempty X] (T : X ≃ₜ X) (k : Type) [Field k] [Finite k],
      IsDedekindFiniteMonoid (ClopenCrossedProduct T k) ↔
        IsOperatorMF (Matrix (Fin 3) (Fin 3) (ClopenCrossedProduct T k))ˣ

/-- The Introduction clause is `prop:bilateral-three` at `n = 3`. -/
theorem printedIntroDirectlyFiniteIffGLThreeMF_of_printedBilateralThree
    (h : PrintedBilateralThree) : PrintedIntroDirectlyFiniteIffGLThreeMF := by
  intro X _ _ _ _ _ T k _ _
  obtain ⟨hMFLEF, hLEFdf, _⟩ := h X T k 3 le_rfl
  exact ⟨fun hdf ↦ hMFLEF.mpr (hLEFdf.mpr hdf), fun hMF ↦ hLEFdf.mp (hMFLEF.mp hMF)⟩

/-- **Printed (tex 1556–1558):** "It is finitely generated, so `L = EL₃(S)` has property (T).
Embed it in `GL₃(R_X)`": the image of `EL₃(S)` under an injective homomorphism has
property (T). -/
theorem hasKazhdanPropertyT_range_of_injective {S : Type} [Ring S]
    (hS : IsFinitelyGeneratedRing S) {G : Type} [Group G]
    (φ : elementaryGroup (Fin 3) S →* G) (hφ : Function.Injective φ) :
    HasKazhdanPropertyT.{0, 0} ↥φ.range :=
  HasKazhdanPropertyT.of_mulEquiv (MonoidHom.ofInjective hφ).symm
    (FullDefectRingEJZUnconditional.ejz S hS 3 le_rfl)

end BilateralThree
end ChainCore
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_axioms GroupApproximation.Manuscript.ChainCore.BilateralThree.printedIntroDirectlyFiniteIffGLThreeMF_of_printedBilateralThree
#audit_axioms GroupApproximation.Manuscript.ChainCore.BilateralThree.hasKazhdanPropertyT_range_of_injective
