import GroupApproximation.Monsters.P13SL2ComparisonAll

/-!
# The lower and outer block embeddings of the matrix models

`SL₂(ℤ)` embeds in `SL₃(ℤ)` as the bottom-right block fixing the first
coordinate, and as the outer-corner block fixing the middle coordinate.
Under these embeddings the matrix models commute with the 23- and
13-block comparison homomorphisms, and rank-two completeness makes both
comparisons injective: all three block pairs of `P13` generate faithful
copies of `SL₂(ℤ)`.
-/

namespace GroupApproximation
namespace SL3BlockEmbeddingAll

open LiteralP13Presentation LiteralP13MatrixModel P13SteinbergCalculus
open SL2BraidPresentation P13SL2ComparisonAll P13UnipotentInjectivity
open SL2Completeness

noncomputable section

/-- The bottom-right block embedding `SL₂(ℤ) →* SL₃(ℤ)`. -/
def blockEmbed23 : SL2 →* SL3 where
  toFun A :=
    ⟨!![1, 0, 0;
        0, (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0,
        (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1;
        0, (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0,
        (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1], by
      have h : (A : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := A.property
      rw [Matrix.det_fin_two] at h
      rw [Matrix.det_fin_three]
      simp
      linear_combination h⟩
  map_one' := Subtype.ext (by
    ext p q
    fin_cases p <;> fin_cases q <;>
      simp [Matrix.SpecialLinearGroup.coe_one])
  map_mul' A B := Subtype.ext (by
    ext p q
    fin_cases p <;> fin_cases q <;>
      (simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Fin.sum_univ_two, Fin.sum_univ_three]; try ring))

/-- The outer-corner block embedding `SL₂(ℤ) →* SL₃(ℤ)`. -/
def blockEmbed13 : SL2 →* SL3 where
  toFun A :=
    ⟨!![(A : Matrix (Fin 2) (Fin 2) ℤ) 0 0, 0,
        (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1;
        0, 1, 0;
        (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0, 0,
        (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1], by
      have h : (A : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := A.property
      rw [Matrix.det_fin_two] at h
      rw [Matrix.det_fin_three]
      simp
      linear_combination h⟩
  map_one' := Subtype.ext (by
    ext p q
    fin_cases p <;> fin_cases q <;>
      simp [Matrix.SpecialLinearGroup.coe_one])
  map_mul' A B := Subtype.ext (by
    ext p q
    fin_cases p <;> fin_cases q <;>
      (simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Fin.sum_univ_two, Fin.sum_univ_three]; try ring))

theorem blockEmbed23_injective : Function.Injective blockEmbed23 := by
  intro A B hAB
  have h := congrArg
    (fun M : SL3 => (M : Matrix (Fin 3) (Fin 3) ℤ)) hAB
  apply Subtype.ext
  ext p q
  fin_cases p <;> fin_cases q
  · exact congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 1 1) h
  · exact congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 1 2) h
  · exact congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 2 1) h
  · exact congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 2 2) h

theorem blockEmbed13_injective : Function.Injective blockEmbed13 := by
  intro A B hAB
  have h := congrArg
    (fun M : SL3 => (M : Matrix (Fin 3) (Fin 3) ℤ)) hAB
  apply Subtype.ext
  ext p q
  fin_cases p <;> fin_cases q
  · exact congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 0 0) h
  · exact congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 0 2) h
  · exact congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 2 0) h
  · exact congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 2 2) h

/-- The 23-block square commutes. -/
theorem toSL3_comp_block23 :
    toSL3.comp sl2ToP13Block23 = blockEmbed23.comp toSL2 := by
  apply PresentedGroup.ext
  intro i
  match i with
  | 0 =>
      simp only [MonoidHom.comp_apply]
      rw [sl2ToP13Block23_of, toSL2_of]
      show toSL3 (x 3 1) = blockEmbed23 (sl2Elem 0)
      rw [toSL3_x, zpow_one]
      exact Subtype.ext (by decide)
  | 1 =>
      simp only [MonoidHom.comp_apply]
      rw [sl2ToP13Block23_of, toSL2_of]
      show toSL3 (x 5 (-1)) = blockEmbed23 (sl2Elem 1)
      rw [toSL3_x, zpow_neg_one, inv_eq_iff_mul_eq_one]
      exact Subtype.ext (by
        rw [Matrix.SpecialLinearGroup.coe_mul]
        decide)

/-- The 13-block square commutes. -/
theorem toSL3_comp_block13 :
    toSL3.comp sl2ToP13Block13 = blockEmbed13.comp toSL2 := by
  apply PresentedGroup.ext
  intro i
  match i with
  | 0 =>
      simp only [MonoidHom.comp_apply]
      rw [sl2ToP13Block13_of, toSL2_of]
      show toSL3 (x 1 1) = blockEmbed13 (sl2Elem 0)
      rw [toSL3_x, zpow_one]
      exact Subtype.ext (by decide)
  | 1 =>
      simp only [MonoidHom.comp_apply]
      rw [sl2ToP13Block13_of, toSL2_of]
      show toSL3 (x 4 (-1)) = blockEmbed13 (sl2Elem 1)
      rw [toSL3_x, zpow_neg_one, inv_eq_iff_mul_eq_one]
      exact Subtype.ext (by
        rw [Matrix.SpecialLinearGroup.coe_mul]
        decide)

/-- The 23-block comparison is injective. -/
theorem sl2ToP13Block23_injective :
    Function.Injective sl2ToP13Block23 := by
  have hcomp : Function.Injective (toSL3.comp sl2ToP13Block23) := by
    rw [toSL3_comp_block23]
    intro g h hgh
    simp only [MonoidHom.comp_apply] at hgh
    exact toSL2_injective (blockEmbed23_injective hgh)
  intro g h hgh
  apply hcomp
  simp only [MonoidHom.comp_apply, hgh]

/-- The 13-block comparison is injective. -/
theorem sl2ToP13Block13_injective :
    Function.Injective sl2ToP13Block13 := by
  have hcomp : Function.Injective (toSL3.comp sl2ToP13Block13) := by
    rw [toSL3_comp_block13]
    intro g h hgh
    simp only [MonoidHom.comp_apply] at hgh
    exact toSL2_injective (blockEmbed13_injective hgh)
  intro g h hgh
  apply hcomp
  simp only [MonoidHom.comp_apply, hgh]

end

end SL3BlockEmbeddingAll
end GroupApproximation
