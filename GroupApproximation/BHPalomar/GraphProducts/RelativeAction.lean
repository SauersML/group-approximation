/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.BHPalomar.GraphProducts.Statement
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# The relative-automorphism action on retractions

The action used for the rank-two relative-automorphism envelope is precomposition on
homomorphisms `H ∗ F₂ → H` that restrict to the identity on `H`. Mixed-identity-freeness
separates elements of the free product, and therefore makes this action faithful.

Translations of the free generators prove transitivity for every `H`, reducing the stabilizer
condition to the identity substitution. This also proves the faithfulness part of type (A)
directly. Finite presentation, finite generation of that stabilizer, and finiteness of diagonal
orbits are separate obligations.
-/

namespace GroupApproximation.BHPalomar.GraphProducts

open Monoid

/-- Every nonidentity word with constants in `H` survives a substitution in `H`. -/
def IsMIF2 (H : Type) [Group H] : Prop :=
  ∀ w : Coprod H (FreeGroup (Fin 2)), w ≠ 1 →
    ∃ φ : Coprod H (FreeGroup (Fin 2)) →* H,
      (∀ h : H, φ (Coprod.inl h) = h) ∧ φ w ≠ 1

/-- Substitutions of the two free generators in `H`, expressed as retractions. -/
def RetractionSpace (H : Type) [Group H] :=
  {φ : Coprod H (FreeGroup (Fin 2)) →* H // ∀ h : H, φ (Coprod.inl h) = h}

variable {H : Type} [Group H]

/-- Relative automorphisms act on substitutions by inverse precomposition. -/
instance retractionSpaceMulAction : MulAction (relAut H 2) (RetractionSpace H) where
  smul α φ := ⟨φ.val.comp (α⁻¹).val.toMonoidHom, by
    intro h
    change φ.val ((α⁻¹).val (Coprod.inl h)) = h
    rw [(α⁻¹).property h, φ.property h]⟩
  one_smul φ := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro w
    rfl
  mul_smul α β φ := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro w
    change φ.val (((α * β)⁻¹).val w) = φ.val ((β⁻¹).val ((α⁻¹).val w))
    simp only [mul_inv_rev, Subgroup.coe_mul, MulAut.mul_apply]

@[simp] theorem retractionSpace_smul_apply (α : relAut H 2) (φ : RetractionSpace H)
    (w : Coprod H (FreeGroup (Fin 2))) :
    (α • φ).val w = φ.val ((α⁻¹).val w) := rfl

/-- Right translations of the two free generators, keeping every constant fixed. -/
def retractionShiftEnd (f : Fin 2 → H) :
    Coprod H (FreeGroup (Fin 2)) →* Coprod H (FreeGroup (Fin 2)) :=
  Coprod.lift Coprod.inl
    (FreeGroup.lift fun i => Coprod.inr (FreeGroup.of i) * Coprod.inl (f i))

@[simp] theorem retractionShiftEnd_inl (f : Fin 2 → H) (h : H) :
    retractionShiftEnd f (Coprod.inl h) = Coprod.inl h := by
  simp [retractionShiftEnd]

@[simp] theorem retractionShiftEnd_generator (f : Fin 2 → H) (i : Fin 2) :
    retractionShiftEnd f (Coprod.inr (FreeGroup.of i)) =
      Coprod.inr (FreeGroup.of i) * Coprod.inl (f i) := by
  simp [retractionShiftEnd]

theorem retractionShiftEnd_inverse (f : Fin 2 → H) :
    (retractionShiftEnd fun i => (f i)⁻¹).comp (retractionShiftEnd f) =
      MonoidHom.id _ := by
  apply Coprod.hom_ext
  · ext h
    simp
  · apply FreeGroup.ext_hom
    intro i
    simp [mul_assoc]

/-- The translations are relative automorphisms. -/
def retractionShift (f : Fin 2 → H) : relAut H 2 :=
  ⟨{ toFun := retractionShiftEnd f
     invFun := retractionShiftEnd fun i => (f i)⁻¹
     left_inv := fun w => DFunLike.congr_fun (retractionShiftEnd_inverse f) w
     right_inv := by
       intro w
       simpa only [inv_inv, MonoidHom.comp_apply, MonoidHom.id_apply] using
         DFunLike.congr_fun (retractionShiftEnd_inverse fun i => (f i)⁻¹) w
     map_mul' := (retractionShiftEnd f).map_mul },
    retractionShiftEnd_inl f⟩

/-- The canonical action is transitive for every base group; no simplicity or MIF is needed. -/
theorem retractionSpace_transitive (φ ψ : RetractionSpace H) :
    ∃ α : relAut H 2, α • φ = ψ := by
  let f : Fin 2 → H := fun i =>
    (φ.val (Coprod.inr (FreeGroup.of i)))⁻¹ * ψ.val (Coprod.inr (FreeGroup.of i))
  refine ⟨(retractionShift f)⁻¹, ?_⟩
  apply Subtype.ext
  apply Coprod.hom_ext
  · ext h
    simp only [MonoidHom.comp_apply, retractionSpace_smul_apply, inv_inv]
    exact (((retractionShift f)⁻¹ • φ).property h).trans (ψ.property h).symm
  · apply FreeGroup.ext_hom
    intro i
    change φ.val ((((retractionShift f)⁻¹)⁻¹).val (Coprod.inr (FreeGroup.of i))) = _
    simp only [inv_inv]
    change φ.val (retractionShiftEnd f (Coprod.inr (FreeGroup.of i))) = _
    rw [retractionShiftEnd_generator, map_mul, φ.property]
    simp only [f, mul_inv_cancel_left]
    rfl

/-- The substitution sending both free generators to the identity. -/
def identityRetraction (H : Type) [Group H] : RetractionSpace H :=
  ⟨Coprod.lift (MonoidHom.id H) 1, by intro h; simp⟩

/-- Transitivity reduces the stabilizer condition to the identity substitution. -/
theorem retractionSpace_stabilizer_fg
    (hfg : (MulAction.stabilizer (relAut H 2) (identityRetraction H)).FG)
    (φ : RetractionSpace H) : (MulAction.stabilizer (relAut H 2) φ).FG := by
  classical
  obtain ⟨α, hα⟩ := retractionSpace_transitive (identityRetraction H) φ
  rw [← hα, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  obtain ⟨T, hT⟩ := hfg
  exact ⟨T.image (MulAut.conj α).toMonoidHom, by
    rw [Finset.coe_image, ← MonoidHom.map_closure, hT]⟩

/-- In a mixed-identity-free group, substitutions distinguish any two words. -/
theorem IsMIF2.eq_of_retractions (hM : IsMIF2 H)
    {a b : Coprod H (FreeGroup (Fin 2))}
    (h : ∀ φ : RetractionSpace H, φ.val a = φ.val b) : a = b := by
  by_contra hab
  obtain ⟨φ, hφ, hne⟩ := hM (a * b⁻¹) (fun h => hab (mul_inv_eq_one.mp h))
  apply hne
  rw [map_mul, map_inv, h ⟨φ, hφ⟩, mul_inv_cancel]

/-- No nontrivial relative automorphism acts trivially on every substitution. -/
theorem IsMIF2.faithful_retractionSpace (hM : IsMIF2 H) :
    FaithfulSMul (relAut H 2) (RetractionSpace H) where
  eq_of_smul_eq_smul := by
    intro α β h
    apply inv_injective
    apply Subtype.ext
    apply MulEquiv.ext
    intro w
    apply hM.eq_of_retractions
    intro φ
    exact congrArg (fun ψ : RetractionSpace H => ψ.val w) (h φ)

/-- With faithfulness discharged, these are exactly the remaining type-(A) conditions. -/
theorem IsMIF2.isTypeA_retractionSpace (hM : IsMIF2 H)
    (hfp : Group.IsFinitelyPresented (relAut H 2))
    (hst : (MulAction.stabilizer (relAut H 2) (identityRetraction H)).FG)
    (horb : Finite (MulAction.orbitRel.Quotient (relAut H 2)
      (RetractionSpace H × RetractionSpace H))) :
    IsTypeA (relAut H 2) (RetractionSpace H) :=
  ⟨hM.faithful_retractionSpace, hfp, retractionSpace_stabilizer_fg hst, horb⟩

end GroupApproximation.BHPalomar.GraphProducts
