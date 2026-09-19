import GroupApproximation.BooneHigman.SteinbergBasic.Naturality
import GroupApproximation.Meta.AxiomGuard

/-!
# Diagonal automorphisms of Steinberg groups (Z1-base, piece Z.1)

For a commutative ring `R`, a finite index type `I` and `d : I → Rˣ`, the assignment
`x_ij(a) ↦ x_ij(d_i a d_j⁻¹)` respects the Steinberg relations. So it defines an endomorphism
`dgHom d` of `St_I(R)`, and it lifts conjugation by the diagonal matrix
`D = diag(d)`:
* `projection_dgHom`: `π(dgHom d u) = D π(u) D⁻¹`;
* `dgHom_mul`, `dgHom_one`: `dgHom (d e) = dgHom d ∘ dgHom e` and `dgHom 1 = id`. So `dgEquiv d`
  is an automorphism.
* `dgHom_mem_K2`: it preserves `K₂(I, R)`.

In the Z1-base route, the vertex stabilizers of the building are conjugates of `SL₃(A)` by
`diag(1,1,p)` and `diag(1,p,p)` in `GL₃(A[1/p])`. These automorphisms carry the Steinberg
presentation of the standard vertex group to the other two (piece Z.6).
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace BTri

open scoped commutatorElement
open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

/-- The rescaled coefficient `d_i a d_j⁻¹`. -/
def dgCoeff (d : I → Rˣ) (i j : I) (a : R) : R :=
  (d i : R) * a * ((d j)⁻¹ : Rˣ)

omit [Fintype I] [DecidableEq I] in
theorem dgCoeff_add (d : I → Rˣ) (i j : I) (a b : R) :
    dgCoeff d i j a + dgCoeff d i j b = dgCoeff d i j (a + b) := by
  unfold dgCoeff
  ring

#audit_axioms dgCoeff_add

omit [Fintype I] [DecidableEq I] in
theorem dgCoeff_mul (d : I → Rˣ) (i j k : I) (a b : R) :
    dgCoeff d i j a * dgCoeff d j k b = dgCoeff d i k (a * b) := by
  unfold dgCoeff
  have h : (((d j)⁻¹ : Rˣ) : R) * (d j : R) = 1 := Units.inv_mul (d j)
  calc (d i : R) * a * (((d j)⁻¹ : Rˣ) : R) * ((d j : R) * b * (((d k)⁻¹ : Rˣ) : R))
      = (d i : R) * a * ((((d j)⁻¹ : Rˣ) : R) * (d j : R)) * b * (((d k)⁻¹ : Rˣ) : R) := by
        ring
    _ = (d i : R) * (a * b) * (((d k)⁻¹ : Rˣ) : R) := by
        rw [h]
        ring

#audit_axioms dgCoeff_mul

omit [Fintype I] [DecidableEq I] in
theorem dgCoeff_one (i j : I) (a : R) : dgCoeff (1 : I → Rˣ) i j a = a := by
  simp [dgCoeff]

#audit_axioms dgCoeff_one

omit [Fintype I] [DecidableEq I] in
theorem dgCoeff_dgCoeff (d e : I → Rˣ) (i j : I) (a : R) :
    dgCoeff d i j (dgCoeff e i j a) = dgCoeff (d * e) i j a := by
  simp only [dgCoeff, Pi.mul_apply, Units.val_mul, mul_inv_rev]
  ring

#audit_axioms dgCoeff_dgCoeff

/-- The generator map of the diagonal automorphism. -/
def dgGen (d : I → Rˣ) (g : SteinbergGenerator I R) : SteinbergGroup I R :=
  x g.row g.column g.row_ne_column (dgCoeff d g.row g.column g.coefficient)

theorem dgGen_kills (d : I → Rˣ) (w : FreeGroup (SteinbergGenerator I R))
    (hw : w ∈ relations (I := I) (R := R)) : FreeGroup.lift (dgGen d) w = 1 := by
  change IsRelation w at hw
  cases hw with
  | add i j hij a b =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of, dgGen]
      change x i j hij (dgCoeff d i j a) * x i j hij (dgCoeff d i j b) *
          (x i j hij (dgCoeff d i j (a + b)))⁻¹ = 1
      rw [x_mul, dgCoeff_add, mul_inv_cancel]
  | commute i j k l hij hkl hjk hli a b =>
      simp only [map_commutatorElement, FreeGroup.lift_apply_of, dgGen]
      change ⁅x i j hij (dgCoeff d i j a), x k l hkl (dgCoeff d k l b)⁆ = 1
      exact (x_commute_of_ne i j k l hij hkl hjk hli _ _).commutator_eq
  | adjacent i j k hij hjk hik a b =>
      simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of, dgGen]
      change ⁅x i j hij (dgCoeff d i j a), x j k hjk (dgCoeff d j k b)⁆ *
          (x i k hik (dgCoeff d i k (a * b)))⁻¹ = 1
      rw [x_commutator i j k hij hjk hik, dgCoeff_mul, mul_inv_cancel]

#audit_axioms dgGen_kills

/-- **The diagonal endomorphism** `x_ij(a) ↦ x_ij(d_i a d_j⁻¹)` of `St_I(R)`. -/
def dgHom (d : I → Rˣ) : SteinbergGroup I R →* SteinbergGroup I R :=
  PresentedGroup.toGroup (f := dgGen d) (dgGen_kills d)

theorem dgHom_x (d : I → Rˣ) (i j : I) (hij : i ≠ j) (a : R) :
    dgHom d (x i j hij a) = x i j hij (dgCoeff d i j a) :=
  PresentedGroup.toGroup.of _

theorem dgHom_one : dgHom (1 : I → Rˣ) = MonoidHom.id (SteinbergGroup I R) := by
  apply PresentedGroup.ext
  rintro ⟨i, j, hij, a⟩
  change dgHom 1 (x i j hij a) = x i j hij a
  rw [dgHom_x, dgCoeff_one]

#audit_axioms dgHom_one

theorem dgHom_mul (d e : I → Rˣ) : (dgHom d).comp (dgHom e) = dgHom (I := I) (d * e) := by
  apply PresentedGroup.ext
  rintro ⟨i, j, hij, a⟩
  change dgHom d (dgHom e (x i j hij a)) = dgHom (d * e) (x i j hij a)
  rw [dgHom_x, dgHom_x, dgHom_x, dgCoeff_dgCoeff]

#audit_axioms dgHom_mul

/-- **The diagonal automorphism** of `St_I(R)`. -/
def dgEquiv (d : I → Rˣ) : SteinbergGroup I R ≃* SteinbergGroup I R :=
  MonoidHom.toMulEquiv (dgHom d) (dgHom d⁻¹)
    (by rw [dgHom_mul, inv_mul_cancel, dgHom_one])
    (by rw [dgHom_mul, mul_inv_cancel, dgHom_one])

@[simp] theorem dgEquiv_apply (d : I → Rˣ) (u : SteinbergGroup I R) :
    dgEquiv d u = dgHom d u :=
  rfl

/-- The diagonal matrix `diag(d)` as a unit. -/
def dgUnit (d : I → Rˣ) : (Matrix I I R)ˣ where
  val := Matrix.diagonal fun k => (d k : R)
  inv := Matrix.diagonal fun k => (((d k)⁻¹ : Rˣ) : R)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [Units.mul_inv, Matrix.diagonal_one]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [Units.inv_mul, Matrix.diagonal_one]

/-- Conjugating an elementary matrix by `diag(d)` rescales its coefficient. -/
theorem dgUnit_conj (d : I → Rˣ) (i j : I) (hij : i ≠ j) (a : R) :
    dgUnit d * elementaryUnit i j hij a * (dgUnit d)⁻¹ =
      elementaryUnit i j hij (dgCoeff d i j a) := by
  apply Units.ext
  change Matrix.diagonal (fun k => (d k : R)) * (1 + Matrix.single i j a) *
      Matrix.diagonal (fun k => (((d k)⁻¹ : Rˣ) : R)) = 1 + Matrix.single i j (dgCoeff d i j a)
  ext k l
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply, Matrix.single_apply]
  by_cases hkl : k = l
  · have hk : ¬(i = k ∧ j = l) := fun h => hij (h.1.trans (hkl.trans h.2.symm))
    simp only [if_pos hkl, if_neg hk, add_zero, mul_one]
    rw [hkl, Units.mul_inv]
  · by_cases h : i = k ∧ j = l
    · obtain ⟨rfl, rfl⟩ := h
      simp [hkl, dgCoeff]
    · simp [hkl, h]

#audit_axioms dgUnit_conj

/-- **The diagonal automorphism lifts conjugation by `diag(d)`.** -/
theorem projection_dgHom (d : I → Rˣ) (u : SteinbergGroup I R) :
    ((projection (dgHom d u) : elementaryGroup I R) : (Matrix I I R)ˣ) =
      dgUnit d * ((projection u : elementaryGroup I R) : (Matrix I I R)ˣ) * (dgUnit d)⁻¹ := by
  have h : (elementaryGroup I R).subtype.comp (projection.comp (dgHom d)) =
      (MulAut.conj (dgUnit d)).toMonoidHom.comp
        ((elementaryGroup I R).subtype.comp projection) := by
    apply PresentedGroup.ext
    rintro ⟨i, j, hij, a⟩
    change ((projection (dgHom d (x i j hij a)) : elementaryGroup I R) : (Matrix I I R)ˣ) =
      dgUnit d * ((projection (x i j hij a) : elementaryGroup I R) : (Matrix I I R)ˣ) *
        (dgUnit d)⁻¹
    rw [dgHom_x, projection_x, projection_x, elementaryRoot_val, elementaryRoot_val, dgUnit_conj]
  exact DFunLike.congr_fun h u

#audit_axioms projection_dgHom

/-- The diagonal automorphism preserves `K₂(I, R)`. -/
theorem dgHom_mem_K2 (d : I → Rˣ) {u : SteinbergGroup I R} (hu : u ∈ K2 I R) :
    dgHom d u ∈ K2 I R := by
  rw [mem_K2_iff] at hu ⊢
  apply Subtype.ext
  rw [projection_dgHom, hu]
  simp

#audit_axioms dgHom_mem_K2

end BTri
end BooneHigmanLinear
end GroupApproximation
