import GroupApproximation.Higman.AmalgamPushout
import GroupApproximation.Algebra.CoprodICyclicReduction

/-!
# The binary free product of torsion-free groups is torsion-free

`Algebra.CoprodICyclicReduction.isPowerTorsionFree_coprodI` proves this for
Mathlib's *indexed* free product.  The Higman--Neumann--Neumann bridge
(`Higman.HNNEmbedding`) is built over the *binary* one, `Monoid.Coprod`, so
this file carries the statement across, by the same two-element-family
identification `Higman.Amalgam` already uses for the amalgam.

With it, and with the repository's `HNNBritton.isPowerTorsionFree_hnn`, both
torsion clauses of the bridge are theorems rather than inputs.
-/

namespace GroupApproximation
namespace Higman

open scoped Monoid.Coprod

variable {G H : Type} [Group G] [Group H]

/-- From the binary free product to the indexed one. -/
def toCoprodI : Monoid.Coprod G H →* Monoid.CoprodI (Amalgam.fam G H) :=
  Monoid.Coprod.lift
    (Monoid.CoprodI.of (M := Amalgam.fam G H) (i := false))
    (Monoid.CoprodI.of (M := Amalgam.fam G H) (i := true))

/-- ... and back. -/
def fromCoprodI : Monoid.CoprodI (Amalgam.fam G H) →* Monoid.Coprod G H :=
  Monoid.CoprodI.lift (fun b => match b with
    | false => (Monoid.Coprod.inl : G →* Monoid.Coprod G H)
    | true => (Monoid.Coprod.inr : H →* Monoid.Coprod G H))

theorem fromCoprodI_comp_toCoprodI :
    (fromCoprodI (G := G) (H := H)).comp toCoprodI
      = MonoidHom.id (Monoid.Coprod G H) := by
  refine Monoid.Coprod.hom_ext ?_ ?_
  · refine MonoidHom.ext fun x => ?_
    show fromCoprodI (toCoprodI (Monoid.Coprod.inl x)) = Monoid.Coprod.inl x
    rfl
  · refine MonoidHom.ext fun x => ?_
    show fromCoprodI (toCoprodI (Monoid.Coprod.inr x)) = Monoid.Coprod.inr x
    rfl

theorem toCoprodI_comp_fromCoprodI :
    (toCoprodI (G := G) (H := H)).comp fromCoprodI
      = MonoidHom.id (Monoid.CoprodI (Amalgam.fam G H)) := by
  refine Monoid.CoprodI.ext_hom _ _ fun b => ?_
  cases b with
  | false =>
      refine MonoidHom.ext fun x => ?_
      show toCoprodI (fromCoprodI (Monoid.CoprodI.of (i := false) x))
        = Monoid.CoprodI.of (i := false) x
      unfold fromCoprodI
      rw [Monoid.CoprodI.lift_of]
      show toCoprodI (Monoid.Coprod.inl x) = _
      unfold toCoprodI
      rw [Monoid.Coprod.lift_apply_inl]
      rfl
  | true =>
      refine MonoidHom.ext fun x => ?_
      show toCoprodI (fromCoprodI (Monoid.CoprodI.of (i := true) x))
        = Monoid.CoprodI.of (i := true) x
      unfold fromCoprodI
      rw [Monoid.CoprodI.lift_of]
      show toCoprodI (Monoid.Coprod.inr x) = _
      unfold toCoprodI
      rw [Monoid.Coprod.lift_apply_inr]
      rfl

/-- The two free products agree. -/
def coprodEquiv : Monoid.Coprod G H ≃* Monoid.CoprodI (Amalgam.fam G H) where
  toFun := toCoprodI
  invFun := fromCoprodI
  left_inv x :=
    congrArg (fun f : Monoid.Coprod G H →* Monoid.Coprod G H => f x)
      fromCoprodI_comp_toCoprodI
  right_inv x :=
    congrArg (fun f : Monoid.CoprodI (Amalgam.fam G H) →*
      Monoid.CoprodI (Amalgam.fam G H) => f x) toCoprodI_comp_fromCoprodI
  map_mul' := map_mul _

/-- **The binary free product of torsion-free groups is torsion-free.** -/
theorem isPowerTorsionFree_coprod (hG : IsPowerTorsionFree G)
    (hH : IsPowerTorsionFree H) : IsPowerTorsionFree (Monoid.Coprod G H) := by
  classical
  have hfam : ∀ b, IsPowerTorsionFree (Amalgam.fam G H b) := by
    intro b
    cases b with
    | false => exact hG
    | true => exact hH
  have hI : IsPowerTorsionFree (Monoid.CoprodI (Amalgam.fam G H)) :=
    CoprodICyclicReduction.isPowerTorsionFree_coprodI hfam
  exact IsPowerTorsionFree.comap hI (coprodEquiv (G := G) (H := H)).toMonoidHom
    (coprodEquiv (G := G) (H := H)).injective

end Higman
end GroupApproximation
