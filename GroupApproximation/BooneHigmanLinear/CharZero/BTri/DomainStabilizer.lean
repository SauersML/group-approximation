import GroupApproximation.BooneHigmanLinear.CharZero.BTri.DomainVertex
import GroupApproximation.Meta.AxiomGuard

/-!
# The stabilizer of the standard lattice vertex

A determinant-one matrix fixing the homothety class of the standard lattice fixes the lattice
itself: determinant valuation forces the homothety exponent to vanish. Consequently its
entries lie in the base ring. Conversely, a determinant-one matrix with integral entries is
the image of an element of `SL₃(A)` and fixes the standard lattice.
-/

namespace GroupApproximation.BooneHigmanLinear.BTri

open Matrix
open scoped Pointwise

variable {A : Type*} [CommRing A] [IsDomain A] {B : Type*} [CommRing B] [Algebra A B]
  {p : A} [IsLocalization.Away p B]

/-- Within one determinant valuation, homothety of lattices is equality. -/
theorem latOf_eq_of_homothetic_of_detVal_eq (hp : Prime p) {g h : GL (Fin 3) B}
    (hgh : Homothetic A B p g h) (hdet : detVal hp g = detVal hp h) :
    latOf A B g = latOf A B h := by
  obtain ⟨a, b, e⟩ := hgh
  rw [smul_latOf, smul_latOf] at e
  obtain ⟨k, hk⟩ := exists_eq_mul_map_of_latOf_eq p hp e
  have hd := congrArg (detVal hp) hk
  rw [detVal_mul, detVal_mul, detVal_mul, detVal_map, detVal_scalar,
    detVal_scalar, hdet] at hd
  have hab : a = b := by omega
  subst b
  have he : h = g * Matrix.GeneralLinearGroup.map (algebraMap A B) k :=
    mul_left_cancel (by simpa only [mul_assoc] using hk)
  rw [he, latOf_mul_map]

#audit_axioms latOf_eq_of_homothetic_of_detVal_eq

/-- The stabilizer of the standard homothety class consists exactly of integral matrices. -/
theorem stabilizer_baseVertex (hp : Prime p) (γ : Matrix.SpecialLinearGroup (Fin 3) B) :
    γ • baseVertex A B p = baseVertex A B p ↔
      ∀ i j, (γ : Matrix (Fin 3) (Fin 3) B) i j ∈ Set.range (algebraMap A B) := by
  constructor
  · intro h
    have hvertex : vertexOf A B p (Matrix.SpecialLinearGroup.toGL γ) = vertexOf A B p 1 := by
      simpa only [sl_smul_def, baseVertex, smul_vertexOf, mul_one] using h
    have hdet : detVal hp (Matrix.SpecialLinearGroup.toGL γ) = detVal hp (1 : GL (Fin 3) B) := by
      rw [detVal_toGL]
      simpa only [map_one] using (detVal_map (B := B) hp (1 : GL (Fin 3) A)).symm
    have hlat := latOf_eq_of_homothetic_of_detVal_eq hp (Quotient.exact hvertex) hdet
    obtain ⟨K, hK⟩ := exists_eq_mul_of_latOf_le hlat.le
    have hK' : (γ : Matrix (Fin 3) (Fin 3) B) = K.map (algebraMap A B) := by
      simpa only [Matrix.GeneralLinearGroup.coe_one, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
        one_mul] using hK
    intro i j
    exact ⟨K i j, (congrFun (congrFun hK' i) j).symm⟩
  · intro h
    choose K hK using h
    have hmap : (algebraMap A B).mapMatrix (Matrix.of K) =
        (γ : Matrix (Fin 3) (Fin 3) B) := by
      ext i j
      exact hK i j
    have hdet : Matrix.det (Matrix.of K) = 1 := by
      apply algebraMap_injective (B := B) hp
      rw [RingHom.map_det, hmap, γ.2, map_one]
    let δ : Matrix.SpecialLinearGroup (Fin 3) A := ⟨Matrix.of K, hdet⟩
    have hgl : Matrix.SpecialLinearGroup.toGL γ =
        Matrix.GeneralLinearGroup.map (algebraMap A B) (Matrix.SpecialLinearGroup.toGL δ) := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      exact (hK i j).symm
    change vertexOf A B p (Matrix.SpecialLinearGroup.toGL γ * 1) = vertexOf A B p 1
    rw [mul_one, hgl, ← one_mul (Matrix.GeneralLinearGroup.map (algebraMap A B)
      (Matrix.SpecialLinearGroup.toGL δ)), vertexOf_mul_map]

#audit_axioms stabilizer_baseVertex

/-- The `stab` field of the one-prime building inputs, with no additional hypothesis. -/
theorem stabilizer_std_zero (hp : Prime p)
    (γ : Matrix.SpecialLinearGroup (Fin 3) (Localization.Away p)) :
    γ • stdVertex A p 0 = stdVertex A p 0 ↔
      ∀ i j, (γ : Matrix (Fin 3) (Fin 3) (Localization.Away p)) i j ∈
        Set.range (algebraMap A (Localization.Away p)) :=
  stabilizer_baseVertex hp γ

#audit_axioms stabilizer_std_zero

end GroupApproximation.BooneHigmanLinear.BTri
