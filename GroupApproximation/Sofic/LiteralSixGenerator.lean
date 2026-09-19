import GroupApproximation.Sofic.LiteralBaseRelations
import GroupApproximation.Sofic.LiteralNonMFEndpoint
import Mathlib.GroupTheory.Rank

/-!
# Six generators suffice for the literal non-MF group

The readable presentation keeps the three translation letters `v₁,v₂,v₃`.
The `x`-action makes two of them redundant:

* `v₃ = x v₁ x⁻¹`;
* `v₂ = x v₃ x⁻¹ = x² v₁ x⁻²`.

Thus `v₁,x,y,z,t,c` generate the same literal group.  This file packages
that observation as an explicit surjection from `FreeGroup (Fin 6)` and as
the rank bound `rank E ≤ 6`.  It does not replace the readable relator list;
the Tietze-deleted relator list is a separate syntactic presentation choice.
-/

namespace GroupApproximation
namespace LiteralSixGenerator

open LiteralNonMFPresentation

noncomputable section

/-- The compressed alphabet, ordered as `v₁,x,y,z,t,c`. -/
abbrev SixGenerator := Fin 6

/-- Evaluation of the six retained letters in the literal group. -/
def sixGenerator : SixGenerator → MarkedGroup
  | 0 => v1
  | 1 => x
  | 2 => y
  | 3 => z
  | 4 => stable
  | 5 => lamp

/-- The induced map from the free group on the six retained letters. -/
def sixGeneratorHom : FreeGroup SixGenerator →* MarkedGroup :=
  FreeGroup.lift sixGenerator

@[simp] theorem sixGeneratorHom_of (i : SixGenerator) :
    sixGeneratorHom (FreeGroup.of i) = sixGenerator i :=
  FreeGroup.lift_apply_of

private theorem v3_eq_x_v1_x_inv : v3 = x * v1 * x⁻¹ := by
  have h := congrArg baseMap LiteralBaseRelations.x_conj_v1
  simpa [LiteralBaseRelations.x, LiteralBaseRelations.v1,
    LiteralBaseRelations.v3] using h.symm

private theorem v2_eq_x_v3_x_inv : v2 = x * v3 * x⁻¹ := by
  have h := congrArg baseMap LiteralBaseRelations.x_conj_v3
  simpa [LiteralBaseRelations.x, LiteralBaseRelations.v2,
    LiteralBaseRelations.v3] using h.symm

/-- The six retained letters generate the literal group. -/
theorem sixGeneratorHom_surjective : Function.Surjective sixGeneratorHom := by
  rw [← MonoidHom.range_eq_top]
  apply top_unique
  intro g _
  apply PresentedGroup.generated_by
    ((relators : Finset (FreeGroup Generator)) : Set (FreeGroup Generator))
    sixGeneratorHom.range
  have hretained (i : SixGenerator) :
      sixGenerator i ∈ sixGeneratorHom.range :=
    ⟨FreeGroup.of i, sixGeneratorHom_of i⟩
  intro i
  cases i with
  | inl j =>
      fin_cases j
      · change v1 ∈ sixGeneratorHom.range
        exact hretained 0
      · change v2 ∈ sixGeneratorHom.range
        rw [v2_eq_x_v3_x_inv, v3_eq_x_v1_x_inv]
        have hx : x ∈ sixGeneratorHom.range :=
          hretained 1
        have hv1 : v1 ∈ sixGeneratorHom.range :=
          hretained 0
        exact sixGeneratorHom.range.mul_mem
          (sixGeneratorHom.range.mul_mem
            hx
            (sixGeneratorHom.range.mul_mem
              (sixGeneratorHom.range.mul_mem hx hv1)
              (sixGeneratorHom.range.inv_mem hx)))
          (sixGeneratorHom.range.inv_mem hx)
      · change v3 ∈ sixGeneratorHom.range
        rw [v3_eq_x_v1_x_inv]
        have hx : x ∈ sixGeneratorHom.range :=
          hretained 1
        have hv1 : v1 ∈ sixGeneratorHom.range :=
          hretained 0
        exact sixGeneratorHom.range.mul_mem
          (sixGeneratorHom.range.mul_mem hx hv1)
          (sixGeneratorHom.range.inv_mem hx)
      · change x ∈ sixGeneratorHom.range
        exact hretained 1
      · change y ∈ sixGeneratorHom.range
        exact hretained 2
      · change z ∈ sixGeneratorHom.range
        exact hretained 3
  | inr j =>
      fin_cases j
      · change stable ∈ sixGeneratorHom.range
        exact hretained 4
      · change lamp ∈ sixGeneratorHom.range
        exact hretained 5

/-- The explicit six-letter surjection supplies finite generation of the
literal group. -/
instance markedGroup_finitelyGenerated : Group.FG MarkedGroup :=
  Group.fg_of_surjective sixGeneratorHom_surjective

/-- The literal finitely presented non-MF group has group rank at most six. -/
theorem literal_rank_le_six : Group.rank MarkedGroup ≤ 6 := by
  classical
  letI : Group.FG (FreeGroup SixGenerator) := inferInstance
  have hfree : Group.rank (FreeGroup SixGenerator) ≤ 6 := by
    let S : Finset (FreeGroup SixGenerator) :=
      Finset.univ.image FreeGroup.of
    have hS : Subgroup.closure (S : Set (FreeGroup SixGenerator)) = ⊤ := by
      simp [S]
    apply (Group.rank_le hS).trans
    calc
      S.card ≤ (Finset.univ : Finset SixGenerator).card := by
        exact Finset.card_image_le
      _ = 6 := by simp [SixGenerator]
  exact (Group.rank_le_of_surjective sixGeneratorHom
    sixGeneratorHom_surjective).trans hfree

/-- Exact six-generator endpoint bundled with the unconditional non-MF
conclusion. -/
theorem literal_sixGenerated_finitelyPresented_nonMF :
    Group.rank MarkedGroup ≤ 6 ∧
      Group.IsFinitelyPresented MarkedGroup ∧
      ¬ IsOperatorMF MarkedGroup :=
  ⟨literal_rank_le_six, inferInstance,
    LiteralNonMFEndpoint.literal_not_isOperatorMF⟩

end
end LiteralSixGenerator
end GroupApproximation
