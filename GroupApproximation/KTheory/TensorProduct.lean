import GroupApproximation.KTheory.Basic
import GroupApproximation.KTheory.TensorKronecker

/-!
# The external product on `K₀`

Given a star pairing `μ : A × B → C` (`StarPairing`), the Kronecker product of projection
matrices `[p], [q] ↦ [p ⊗_μ q]` descends through stable isomorphism in each variable and through
block sums, so it defines a map additive in each variable

  `KZero.extProd μ : KZero A →+ KZero B →+ KZero C`,  `extProd μ [p] [q] = [p ⊗_μ q]`.

For `μ = (a, b) ↦ a ⊗ b` into a C*-tensor product this is the external product
`K₀(A) ⊗ K₀(B) → K₀(A ⊗ B)` (Blackadar, *K-Theory for Operator Algebras*, §9.2).

The descent is move by move: a Murray–von Neumann implementer tensors with the other factor
(`murrayVonNeumannEquiv_kron_left`), a relabelling tensors to a relabelling
(`kron_submatrix_left`), and padding by zeros tensors to padding up to the reindexing
`finProdSumLeft` (`kron_blockSum_left`).  The Grothendieck group is reached by two applications
of its universal property.
-/

noncomputable section

namespace GroupApproximation
namespace KTheory

open Matrix

variable {A B C : Type*} [NonUnitalSemiring A] [StarRing A] [NonUnitalSemiring B] [StarRing B]
  [NonUnitalSemiring C] [StarRing C] (μ : StarPairing A B C)

namespace Cycle

/-- The external product of cycles: the Kronecker product of the presenting projections. -/
def extProd (x : Cycle A) (y : Cycle B) : Cycle C :=
  ⟨x.size * y.size, kron μ x.proj y.proj, isStarProjection_kron μ x.isProj y.isProj⟩

@[simp] theorem size_extProd (x : Cycle A) (y : Cycle B) :
    (extProd μ x y).size = x.size * y.size := rfl

@[simp] theorem proj_extProd (x : Cycle A) (y : Cycle B) :
    (extProd μ x y).proj = kron μ x.proj y.proj := rfl

/-- One elementary move on the left factor survives the external product. -/
theorem Step.rel_extProd_left {x x' : Cycle A} (h : Step x x') (y : Cycle B) :
    Rel (extProd μ x y) (extProd μ x' y) := by
  obtain ⟨n, q, hq⟩ := y
  cases h with
  | @mvn m p p' hp hp' hpp' =>
      exact rel_of_step (Step.mvn (murrayVonNeumannEquiv_kron_left μ hpp' hq))
  | @reindex m m' p hp e =>
      exact rel_reindex_eq _ _ (finProdCongr e (Equiv.refl (Fin n)))
        (kron_submatrix_left μ e p q).symm
  | @pad m p hp a =>
      refine rel_trans (rel_of_step (Step.pad (a * n)))
        (rel_reindex_eq _ _ (finProdSumLeft m a n) ?_)
      have h := kron_blockSum_left μ p (0 : Matrix (Fin a) (Fin a) A) q
      rw [kron_zero_left μ q] at h
      exact h

/-- One elementary move on the right factor survives the external product. -/
theorem Step.rel_extProd_right (x : Cycle A) {y y' : Cycle B} (h : Step y y') :
    Rel (extProd μ x y) (extProd μ x y') := by
  obtain ⟨m, p, hp⟩ := x
  cases h with
  | @mvn n q q' hq hq' hqq' =>
      exact rel_of_step (Step.mvn (murrayVonNeumannEquiv_kron_right μ hp hqq'))
  | @reindex n n' q hq e =>
      exact rel_reindex_eq _ _ (finProdCongr (Equiv.refl (Fin m)) e)
        (kron_submatrix_right μ e p q).symm
  | @pad n q hq a =>
      refine rel_trans (rel_of_step (Step.pad (m * a)))
        (rel_reindex_eq _ _ (finProdSumRight m n a) ?_)
      have h := kron_blockSum_right μ p q (0 : Matrix (Fin a) (Fin a) B)
      rw [kron_zero_right μ p] at h
      exact h

theorem rel_extProd_left {x x' : Cycle A} (h : Rel x x') (y : Cycle B) :
    Rel (extProd μ x y) (extProd μ x' y) := by
  induction h with
  | rel _ _ hxy => exact Step.rel_extProd_left μ hxy y
  | refl _ => exact rel_refl _
  | symm _ _ _ ih => exact rel_symm ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact rel_trans ih₁ ih₂

theorem rel_extProd_right (x : Cycle A) {y y' : Cycle B} (h : Rel y y') :
    Rel (extProd μ x y) (extProd μ x y') := by
  induction h with
  | rel _ _ hyy => exact Step.rel_extProd_right μ x hyy
  | refl _ => exact rel_refl _
  | symm _ _ _ ih => exact rel_symm ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact rel_trans ih₁ ih₂

/-- The external product distributes over the block sum on the left. -/
theorem rel_extProd_add_left (x x' : Cycle A) (y : Cycle B) :
    Rel (extProd μ (x + x') y) (extProd μ x y + extProd μ x' y) :=
  rel_symm (rel_reindex_eq _ _ (finProdSumLeft x.size x'.size y.size)
    (kron_blockSum_left μ x.proj x'.proj y.proj))

/-- The external product distributes over the block sum on the right. -/
theorem rel_extProd_add_right (x : Cycle A) (y y' : Cycle B) :
    Rel (extProd μ x (y + y')) (extProd μ x y + extProd μ x y') :=
  rel_symm (rel_reindex_eq _ _ (finProdSumRight x.size y.size y'.size)
    (kron_blockSum_right μ x.proj y.proj y'.proj))

theorem rel_extProd_zero_left (y : Cycle B) : Rel (extProd μ (0 : Cycle A) y) 0 :=
  rel_reindex_eq _ _ (finCongr (Nat.zero_mul y.size).symm) (by ext i j; exact Fin.elim0 i)

theorem rel_extProd_zero_right (x : Cycle A) : Rel (extProd μ x (0 : Cycle B)) 0 :=
  rel_reindex_eq _ _ (finCongr (Nat.mul_zero x.size).symm) (by ext i j; exact Fin.elim0 i)

end Cycle

namespace VMonoid

/-- The external product with a fixed cycle on the left, on classes. -/
def extProdRight (x : Cycle A) : VMonoid B →+ VMonoid C where
  toFun := Quotient.map (Cycle.extProd μ x) fun _ _ h => Cycle.rel_extProd_right μ x h
  map_zero' := mk_eq_mk_of_rel (Cycle.rel_extProd_zero_right μ x)
  map_add' a b := Quotient.inductionOn₂ a b fun y y' =>
    mk_eq_mk_of_rel (Cycle.rel_extProd_add_right μ x y y')

@[simp] theorem extProdRight_mk (x : Cycle A) (y : Cycle B) :
    extProdRight μ x (mk y) = mk (Cycle.extProd μ x y) := rfl

/-- The external product on the monoids of classes, additive in each variable. -/
def extProd : VMonoid A →+ VMonoid B →+ VMonoid C where
  toFun := Quotient.lift (extProdRight μ) fun _ _ h => AddMonoidHom.ext fun b =>
    Quotient.inductionOn b fun y => mk_eq_mk_of_rel (Cycle.rel_extProd_left μ h y)
  map_zero' := AddMonoidHom.ext fun b => Quotient.inductionOn b fun y =>
    mk_eq_mk_of_rel (Cycle.rel_extProd_zero_left μ y)
  map_add' a a' := Quotient.inductionOn₂ a a' fun x x' => AddMonoidHom.ext fun b =>
    Quotient.inductionOn b fun y => mk_eq_mk_of_rel (Cycle.rel_extProd_add_left μ x x' y)

@[simp] theorem extProd_mk (x : Cycle A) (y : Cycle B) :
    extProd μ (mk x) (mk y) = mk (Cycle.extProd μ x y) := rfl

end VMonoid

namespace KZero

private theorem kzero_hom_ext {D : Type*} [NonUnitalSemiring D] [StarRing D] {G : Type*}
    [AddCommGroup G] {f g : KZero D →+ G} (h : ∀ x : Cycle D, f (mk x) = g (mk x)) : f = g := by
  apply Algebra.GrothendieckAddGroup.lift.symm.injective
  exact AddMonoidHom.ext fun v => Quotient.inductionOn v fun x => h x

private theorem kzero_mk_eq_of_rel {D : Type*} [NonUnitalSemiring D] [StarRing D]
    {x y : Cycle D} (h : Cycle.Rel x y) : mk x = mk y := by
  show Algebra.GrothendieckAddGroup.of (VMonoid.mk x) = Algebra.GrothendieckAddGroup.of (VMonoid.mk y)
  rw [VMonoid.mk_eq_mk_of_rel h]

/-- The external product with a fixed class of the monoid on the left. -/
def extProdV (v : VMonoid A) : KZero B →+ KZero C :=
  Algebra.GrothendieckAddGroup.lift ((Algebra.GrothendieckAddGroup.of).comp (VMonoid.extProd μ v))

theorem extProdV_mk (x : Cycle A) (y : Cycle B) :
    extProdV μ (VMonoid.mk x) (mk y) = mk (Cycle.extProd μ x y) :=
  DFunLike.congr_fun (Algebra.GrothendieckAddGroup.lift.symm_apply_apply
    ((Algebra.GrothendieckAddGroup.of).comp (VMonoid.extProd μ (VMonoid.mk x)))) (VMonoid.mk y)

/-- The external product, additive in the monoid variable. -/
def extProdAux : VMonoid A →+ KZero B →+ KZero C where
  toFun := extProdV μ
  map_zero' := kzero_hom_ext fun y => by
    show extProdV μ (VMonoid.mk 0) (mk y) = (0 : KZero B →+ KZero C) (mk y)
    rw [extProdV_mk, kzero_mk_eq_of_rel (Cycle.rel_extProd_zero_left μ y), mk_zero,
      AddMonoidHom.zero_apply]
  map_add' v v' := Quotient.inductionOn₂ v v' fun x x' => kzero_hom_ext fun y => by
    show extProdV μ (VMonoid.mk (x + x')) (mk y) =
      extProdV μ (VMonoid.mk x) (mk y) + extProdV μ (VMonoid.mk x') (mk y)
    rw [extProdV_mk, extProdV_mk, extProdV_mk,
      kzero_mk_eq_of_rel (Cycle.rel_extProd_add_left μ x x' y), mk_add]

/-- **The external product on `K₀`** along a star pairing, additive in each variable:
`extProd μ [p] [q] = [p ⊗_μ q]` (Blackadar, §9.2). -/
def extProd : KZero A →+ KZero B →+ KZero C :=
  Algebra.GrothendieckAddGroup.lift (extProdAux μ)

@[simp] theorem extProd_mk (x : Cycle A) (y : Cycle B) :
    extProd μ (mk x) (mk y) = mk (Cycle.extProd μ x y) :=
  (DFunLike.congr_fun (DFunLike.congr_fun
    (Algebra.GrothendieckAddGroup.lift.symm_apply_apply (extProdAux μ)) (VMonoid.mk x))
    (mk y)).trans (extProdV_mk μ x y)

end KZero

end KTheory
end GroupApproximation
