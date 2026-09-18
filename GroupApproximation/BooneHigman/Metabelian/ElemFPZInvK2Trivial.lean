import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2NilGeneric
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2BaseTrivial
import GroupApproximation.Meta.AxiomGuard

/-!
# The nil gap over the zero ring, in particular over `ℤ[1/0]`

Lane `bh-met-44`, helper module.  Lane `bh-met-37` isolated
`CharZeroK2NilGapStatement := ∀ m, PolyK2NilGapStatementOver (Localization.Away (m : ℤ)) 4`
(module `ElemFPCharZeroK2NilEndpoint`).  This module proves the degenerate instance `m = 0`
with no hypothesis.

* `k2_eq_one_of_subsingleton`: over the zero ring every element of `K₂(I, R)` is `1`, because the
  whole Steinberg group is trivial (`steinbergGroup_subsingleton`, lane `bh-met-36`).
* `polyK2NilGapOver_of_subsingleton`: if `A` is the zero ring then so are `A[s_1..s_k]` and
  `A[s_1..s_k][t]` (`RingHom.codomain_trivial` along `C`).  So both halves of the gap pair hold at
  every offset `d`: an element that is `1` dies at its own rank `M = N`, and is trivial.
* `polyK2NilPosOver_of_subsingleton`: the same for the vanishing statement.
* `charZeroK2NilGap_zero`: `ℤ[1/0]` is the zero ring
  (`localizationAway_subsingleton_of_eq_zero`), so the gap pair holds over it at offset `4`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigman.Metabelian.ElemFP

/-- Over the zero ring every element of `K₂(I, R)` is trivial. -/
theorem k2_eq_one_of_subsingleton {I R : Type*} [Fintype I] [DecidableEq I] [Ring R]
    [Subsingleton R] (u : K2 I R) : u = 1 := by
  have hs : Subsingleton (SteinbergGroup I R) := steinbergGroup_subsingleton
  exact Subtype.ext (Subsingleton.elim _ _)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.k2_eq_one_of_subsingleton

/-- **The gap pair over the zero ring**, at every offset `d`. -/
theorem polyK2NilGapOver_of_subsingleton (A : Type*) [CommRing A] [Subsingleton A] (d : ℕ) :
    PolyK2NilGapStatementOver A d := by
  refine ⟨fun k N _ _ _ ↦ ⟨N, le_rfl, ?_⟩, fun k _ _ _ _ ↦ ?_⟩
  · have hS : Subsingleton (MvPolynomial (Fin k) A) :=
      RingHom.codomain_trivial (MvPolynomial.C : A →+* MvPolynomial (Fin k) A)
    have hP : Subsingleton (Polynomial (MvPolynomial (Fin k) A)) :=
      RingHom.codomain_trivial
        (Polynomial.C : MvPolynomial (Fin k) A →+* Polynomial (MvPolynomial (Fin k) A))
    exact k2_eq_one_of_subsingleton _
  · have hS : Subsingleton (MvPolynomial (Fin k) A) :=
      RingHom.codomain_trivial (MvPolynomial.C : A →+* MvPolynomial (Fin k) A)
    exact k2_eq_one_of_subsingleton _

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.polyK2NilGapOver_of_subsingleton

/-- **Vanishing of `ker ev₀` over the zero ring**, at every offset `d`. -/
theorem polyK2NilPosOver_of_subsingleton (A : Type*) [CommRing A] [Subsingleton A] (d : ℕ) :
    PolyK2NilPosStatementOver A d := by
  intro k _ _ _ u _
  have hS : Subsingleton (MvPolynomial (Fin k) A) :=
    RingHom.codomain_trivial (MvPolynomial.C : A →+* MvPolynomial (Fin k) A)
  exact k2_eq_one_of_subsingleton u

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.polyK2NilPosOver_of_subsingleton

/-- **Proved case `m = 0`.**  The gap pair holds over `ℤ[1/0]`, which is the zero ring. -/
theorem charZeroK2NilGap_zero :
    PolyK2NilGapStatementOver (Localization.Away ((0 : ℕ) : ℤ)) 4 := by
  have hs : Subsingleton (Localization.Away ((0 : ℕ) : ℤ)) :=
    localizationAway_subsingleton_of_eq_zero Nat.cast_zero
  exact polyK2NilGapOver_of_subsingleton _ 4

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.charZeroK2NilGap_zero

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
