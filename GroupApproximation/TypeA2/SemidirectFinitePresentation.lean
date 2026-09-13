import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.FinitelyPresentedGroup
import GroupApproximation.GroupTheory.FinitePresentationExtension

/-!
# Finite presentation of semidirect products

The actor of the type `[A_2]` witness is a semidirect product `Γ ⋊ F_m` of a finitely presented
group by a free group of finite rank.

* `isFinitelyPresented_semidirectProduct`: if `N` and `H` are finitely presented, then so is
  `N ⋊[φ] H`.  The image of `inl` is the kernel of `rightHom` and is isomorphic to `N`, the quotient
  by it is isomorphic to `H`, and P. Hall's theorem `isFinitelyPresented_of_normal` applies.
* `isFinitelyPresented_semidirectProduct_freeGroup`: the case `H = FreeGroup (Fin m)`.
-/

namespace GroupApproximation
namespace TypeA2

open SemidirectProduct

variable {N H : Type*} [Group N] [Group H]

/-- **Semidirect products of finitely presented groups are finitely presented.** -/
theorem isFinitelyPresented_semidirectProduct (φ : H →* MulAut N) [Group.IsFinitelyPresented N]
    [Group.IsFinitelyPresented H] : Group.IsFinitelyPresented (N ⋊[φ] H) := by
  haveI : Group.IsFinitelyPresented (rightHom : N ⋊[φ] H →* H).ker :=
    Group.IsFinitelyPresented.equiv
      ((MonoidHom.ofInjective (inl_injective (φ := φ))).trans
        (MulEquiv.subgroupCongr (range_inl_eq_ker_rightHom (φ := φ))))
  haveI : Group.IsFinitelyPresented ((N ⋊[φ] H) ⧸ (rightHom : N ⋊[φ] H →* H).ker) :=
    Group.IsFinitelyPresented.equiv
      (QuotientGroup.quotientKerEquivOfSurjective (rightHom : N ⋊[φ] H →* H)
        (rightHom_surjective (φ := φ))).symm
  exact FinitePresentationExtension.isFinitelyPresented_of_normal (rightHom : N ⋊[φ] H →* H).ker

/-- A finitely presented group extended by a free group of finite rank is finitely presented. -/
theorem isFinitelyPresented_semidirectProduct_freeGroup {m : ℕ}
    (φ : FreeGroup (Fin m) →* MulAut N) [Group.IsFinitelyPresented N] :
    Group.IsFinitelyPresented (N ⋊[φ] FreeGroup (Fin m)) :=
  isFinitelyPresented_semidirectProduct φ

end TypeA2
end GroupApproximation
