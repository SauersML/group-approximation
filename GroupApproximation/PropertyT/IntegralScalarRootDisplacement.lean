import GroupApproximation.PropertyT.IntegralColumnPlaneRootReduction
import GroupApproximation.Monsters.P13InvariantProjection
import GroupApproximation.Monsters.SL3ElementaryGeneration

/-!
# Uniform control of integral scalar roots

The direct additive estimate for `x_ij(m)` grows with `|m|`.  This file removes
that loss unconditionally.  The scalar matrices form the image of
`SL₃(ℤ)`, and the exact six-generator `P13` projection estimate controls the
whole image with one constant.  Thus every integer scalar coefficient in every
elementary root has displacement at most `12000 * delta` whenever the integral
control set moves the vector by less than `delta`.

This is the coefficient-independent estimate on the degree-zero stage.  It is
the input needed to keep integer coefficients out of subsequent finite-degree
bounds; it does not assert the still-missing bound uniform in the degree.
-/

namespace GroupApproximation

universe u v

namespace IntegralScalarRootDisplacement

open IntegralCharacterMass IntegralColumnPlaneRootReduction
open LiteralP13MatrixModel LiteralP13Presentation P13InvariantProjection

/-- The underlying matrix unit of an element of `SL₃(ℤ)`. -/
def sl3UnitsHom : SL3 →* (Matrix (Fin 3) (Fin 3) ℤ)ˣ where
  toFun A :=
    { val := A.1
      inv := (A⁻¹).1
      val_inv := by
        have h := congrArg
          (fun B : SL3 => (B : Matrix (Fin 3) (Fin 3) ℤ))
          (mul_inv_cancel A)
        simpa only [Matrix.SpecialLinearGroup.coe_mul,
          Matrix.SpecialLinearGroup.coe_one] using h
      inv_val := by
        have h := congrArg
          (fun B : SL3 => (B : Matrix (Fin 3) (Fin 3) ℤ))
          (inv_mul_cancel A)
        simpa only [Matrix.SpecialLinearGroup.coe_mul,
          Matrix.SpecialLinearGroup.coe_one] using h }
  map_one' := by
    apply Units.ext
    rfl
  map_mul' A B := by
    apply Units.ext
    rfl

/-- The ordered root represented by each of the six `P13` generators. -/
def p13Root : Fin 6 → A2Root :=
  ![⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩,
    ⟨(1, 0), by decide⟩, ⟨(1, 2), by decide⟩,
    ⟨(2, 0), by decide⟩, ⟨(2, 1), by decide⟩]

@[simp] theorem sl3UnitsHom_elem (q : Fin 6) :
    sl3UnitsHom (elem q) =
      elementaryUnit (p13Root q).1.1 (p13Root q).1.2 (p13Root q).2 1 := by
  fin_cases q <;> apply Units.ext <;> decide

@[simp] theorem sl3UnitsHom_tv (i j : Fin 3) (hij : i ≠ j) (m : ℤ) :
    sl3UnitsHom (SL3ElementaryGeneration.tv i j hij m) =
      elementaryUnit i j hij m := by
  apply Units.ext
  rfl

/-- Every determinant-one integral matrix is elementary, bundled as a map
from `SL₃(ℤ)` to `EL₃(ℤ)`. -/
theorem sl3UnitsHom_mem_elementaryGroup (A : SL3) :
    sl3UnitsHom A ∈ elementaryGroup (Fin 3) ℤ := by
  let K : Subgroup SL3 :=
    (elementaryGroup (Fin 3) ℤ).comap sl3UnitsHom
  have hle : SL3ElementaryGeneration.H ≤ K := by
    rw [SL3ElementaryGeneration.H, Subgroup.closure_le]
    rintro _ ⟨q, rfl⟩
    change sl3UnitsHom (elem q) ∈ elementaryGroup (Fin 3) ℤ
    rw [show sl3UnitsHom (elem q) =
      elementaryUnit (p13Root q).1.1 (p13Root q).1.2 (p13Root q).2 1 from
        sl3UnitsHom_elem q]
    exact elementaryUnit_mem _ _ _ _
  exact hle (SL3ElementaryGeneration.mem_H A)

/-- The scalar copy of `SL₃(ℤ)` inside the integral elementary group. -/
def sl3ToElementary : SL3 →* elementaryGroup (Fin 3) ℤ :=
  sl3UnitsHom.codRestrict (elementaryGroup (Fin 3) ℤ)
    sl3UnitsHom_mem_elementaryGroup

/-- The `P13` scalar subgroup inside `EL₃(ℤ⟨X⟩)`. -/
noncomputable def integralScalarHom (X : Type u) :
    P13 →* elementaryGroup (Fin 3) (FreeAlgebra ℤ X) :=
  (elementaryGroupMap (ι := Fin 3)
    (Int.castRingHom (FreeAlgebra ℤ X))).comp
      (sl3ToElementary.comp toSL3)

@[simp] theorem integralScalarHom_generator (X : Type u) (q : Fin 6) :
    integralScalarHom X (p13Generator q) =
      elementaryRoot (p13Root q).1.1 (p13Root q).1.2 (p13Root q).2 1 := by
  apply Subtype.ext
  change elementaryMatrixUnitMap (Int.castRingHom (FreeAlgebra ℤ X))
      (sl3UnitsHom (toSL3 (p13Generator q))) = _
  have hto : toSL3 (p13Generator q) = elem q := by
    change toSL3 (PresentedGroup.of q) = elem q
    exact toSL3_of q
  rw [hto, sl3UnitsHom_elem,
    elementaryMatrixUnitMap_elementaryUnit]
  simp

/-- Every scalar root lies in the image of the scalar `P13` map. -/
theorem exists_integralScalarHom_eq_scalarRoot
    (X : Type u) (i j : Fin 3) (hij : i ≠ j) (m : ℤ) :
    ∃ p : P13, integralScalarHom X p =
      elementaryRoot i j hij (algebraMap ℤ (FreeAlgebra ℤ X) m) := by
  obtain ⟨p, hp⟩ := SL3ElementaryGeneration.toSL3_surjective
    (SL3ElementaryGeneration.tv i j hij m)
  refine ⟨p, ?_⟩
  apply Subtype.ext
  change elementaryMatrixUnitMap (Int.castRingHom (FreeAlgebra ℤ X))
      (sl3UnitsHom (toSL3 p)) = _
  rw [hp, sl3UnitsHom_tv, elementaryMatrixUnitMap_elementaryUnit]
  simp

/-- Uniform, coefficient-independent displacement on the degree-zero integral
stage.  The constant is the exact `P13` projection constant times the six
displayed generators and the final factor two for displacement from the fixed
part: `2 * 1000 * 6 = 12000`. -/
theorem norm_integral_scalarRoot_displacement_le_of_controlSet_near
    (X : Type u) [Fintype X]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (rho : elementaryGroup (Fin 3) (FreeAlgebra ℤ X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (delta : ℝ)
    (hnear : ∀ s ∈ integralControlSet X, ‖rho s z - z‖ < delta)
    (i j : Fin 3) (hij : i ≠ j) (m : ℤ) :
    ‖rho (elementaryRoot i j hij
      (algebraMap ℤ (FreeAlgebra ℤ X) m)) z - z‖ ≤ 12000 * delta := by
  obtain ⟨p, hp⟩ := exists_integralScalarHom_eq_scalarRoot X i j hij m
  let rhoP : P13 →* (E ≃ₗᵢ[ℝ] E) := rho.comp (integralScalarHom X)
  let y : E := KazhdanFixedSpace.fixedProjection rhoP ⊤ z
  have hgen (q : Fin 6) :
      ‖rhoP (p13Generator q) z - z‖ < delta := by
    rw [show rhoP (p13Generator q) =
      rho (elementaryRoot (p13Root q).1.1 (p13Root q).1.2
        (p13Root q).2 1) by simp [rhoP]]
    exact norm_integral_unitRoot_displacement_lt_of_controlSet_near
      X rho z delta hnear _ _ _
  have hsum : (∑ q : Fin 6, ‖rhoP (p13Generator q) z - z‖) < 6 * delta := by
    calc
      (∑ q : Fin 6, ‖rhoP (p13Generator q) z - z‖) <
          ∑ _q : Fin 6, delta :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
          (fun q _ ↦ hgen q)
      _ = 6 * delta := by simp
  have hdist : ‖z - y‖ ≤
      1000 * ∑ q : Fin 6, ‖rhoP (p13Generator q) z - z‖ :=
    t1_06_norm_sub_fixedProjection_le rhoP z
  have hyp : rhoP p y = y :=
    KazhdanFixedSpace.fixedProjection_mem rhoP ⊤ z
      ⟨p, Subgroup.mem_top p⟩
  have hmove : ‖rhoP p z - z‖ ≤ 2 * ‖z - y‖ := by
    calc
      ‖rhoP p z - z‖ = ‖rhoP p (z - y) - (z - y)‖ := by
        simp only [map_sub, hyp]
        congr 1
        abel
      _ ≤ ‖rhoP p (z - y)‖ + ‖z - y‖ := norm_sub_le _ _
      _ = 2 * ‖z - y‖ := by rw [(rhoP p).norm_map]; ring
  rw [← hp]
  change ‖rhoP p z - z‖ ≤ 12000 * delta
  calc
    ‖rhoP p z - z‖ ≤ 2 * ‖z - y‖ := hmove
    _ ≤ 2 * (1000 * ∑ q : Fin 6,
        ‖rhoP (p13Generator q) z - z‖) := by linarith
    _ ≤ 12000 * delta := by nlinarith

end IntegralScalarRootDisplacement

end GroupApproximation
