import GroupApproximation.Monsters.P13SL2Comparison

/-!
# The top-left block embedding of the matrix models

The special linear group of rank two embeds in rank three as the
top-left block, fixing the last coordinate.  Under this embedding the
two matrix models are compatible with the comparison homomorphism of
presentations: the square

  `toSL3 ∘ sl2ToP13 = blockEmbed ∘ toSL2`

commutes.  In particular any element of the rank-two braid presentation
that dies in `SL₂(ℤ)` is sent by the comparison map into the kernel of
the rank-three matrix model, and conversely once the rank-two
presentation is known to be complete, the copy of the Weyl pair inside
`P13` maps isomorphically onto the block copy of `SL₂(ℤ)`.
-/

namespace GroupApproximation
namespace SL3BlockEmbedding

open LiteralP13Presentation P13SteinbergCalculus LiteralP13MatrixModel
open SL2BraidPresentation P13SL2Comparison P13UnipotentInjectivity

noncomputable section

/-- The top-left block embedding `SL₂(ℤ) →* SL₃(ℤ)`. -/
def blockEmbed : SL2 →* SL3 where
  toFun A :=
    ⟨!![(A : Matrix (Fin 2) (Fin 2) ℤ) 0 0,
        (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1, 0;
        (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0,
        (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1, 0;
        0, 0, 1], by
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

@[simp] theorem blockEmbed_coe (A : SL2) :
    ((blockEmbed A : SL3) : Matrix (Fin 3) (Fin 3) ℤ) =
      !![(A : Matrix (Fin 2) (Fin 2) ℤ) 0 0,
         (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1, 0;
         (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0,
         (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1, 0;
         0, 0, 1] :=
  rfl

/-- The two matrix models agree through the comparison homomorphism. -/
theorem toSL3_comp_sl2ToP13 :
    toSL3.comp sl2ToP13 = blockEmbed.comp toSL2 := by
  apply PresentedGroup.ext
  intro i
  match i with
  | 0 =>
      simp only [MonoidHom.comp_apply]
      rw [sl2ToP13_of_zero, toSL2_of, toSL3_x, zpow_one]
      exact Subtype.ext (by decide)
  | 1 =>
      simp only [MonoidHom.comp_apply]
      rw [sl2ToP13_of_one, toSL2_of, toSL3_x, zpow_neg_one,
        inv_eq_iff_mul_eq_one]
      exact Subtype.ext (by
        rw [Matrix.SpecialLinearGroup.coe_mul]
        decide)

theorem toSL3_sl2ToP13 (g : SL2P) :
    toSL3 (sl2ToP13 g) = blockEmbed (toSL2 g) := by
  have h := congrArg (fun φ : SL2P →* SL3 => φ g) toSL3_comp_sl2ToP13
  simpa using h

end

end SL3BlockEmbedding
end GroupApproximation
