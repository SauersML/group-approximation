import GroupApproximation.Monsters.P13WeylCalculus
import GroupApproximation.Monsters.SL2BraidPresentation

/-!
# The rank-two braid presentation maps into P13

The braid relation for `x₁₂(1)` and `x₂₁(-1)` and the fourth-power
relator both hold in `P13` (`P13WeylCalculus`), so the assignment
`a ↦ x₁₂(1)`, `b ↦ x₂₁(-1)` kills both relators of the rank-two braid
presentation and induces the canonical comparison homomorphism

  `sl2ToP13 : SL2P →* P13`.

Its image is the copy of the rank-two Weyl pair inside `P13`; the
comparison is the seed of the parabolic peeling in the completeness
programme.
-/

namespace GroupApproximation
namespace P13SL2Comparison

open LiteralP13Presentation P13SteinbergCalculus P13WeylCalculus
open SL2BraidPresentation PresentedGroupRelatorReplay

noncomputable section

/-- The generator assignment `a ↦ x₁₂(1)`, `b ↦ x₂₁(-1)`. -/
def sl2ToP13Gen : Fin 2 → P13
  | 0 => x 0 1
  | 1 => x 2 (-1)

private theorem lift_relator_zero :
    FreeGroup.lift sl2ToP13Gen (sl2Relator 0) = 1 := by
  calc FreeGroup.lift sl2ToP13Gen (sl2Relator 0)
      = x 0 1 * x 2 (-1) * x 0 1 *
        (x 2 (-1) * x 0 1 * x 2 (-1))⁻¹ := by
        simp only [sl2Relator, sl2RelatorLetters, word, FreeGroup.lift_mk,
          List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          cond_true, cond_false, sl2ToP13Gen]
        group
    _ = 1 := by
      rw [braid]
      group

private theorem lift_relator_one :
    FreeGroup.lift sl2ToP13Gen (sl2Relator 1) = 1 := by
  calc FreeGroup.lift sl2ToP13Gen (sl2Relator 1)
      = x 0 1 * x 2 (-1) * x 0 1 *
        (x 0 1 * x 2 (-1) * x 0 1) * (x 0 1 * x 2 (-1) * x 0 1) *
        (x 0 1 * x 2 (-1) * x 0 1) := by
        simp only [sl2Relator, sl2RelatorLetters, word, FreeGroup.lift_mk,
          List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          cond_true, sl2ToP13Gen]
        group
    _ = 1 := w_pow_four

theorem lift_sl2ToP13Gen_relator_eq_one (i : Fin 2) :
    FreeGroup.lift sl2ToP13Gen (sl2Relator i) = 1 := by
  fin_cases i
  · exact lift_relator_zero
  · exact lift_relator_one

theorem lift_sl2ToP13Gen_eq_one_of_mem {r : FreeGroup SL2BraidGenerator}
    (hr : r ∈ (sl2Relators : Set (FreeGroup SL2BraidGenerator))) :
    FreeGroup.lift sl2ToP13Gen r = 1 := by
  obtain ⟨i, rfl⟩ := (mem_sl2Relators_iff r).mp hr
  exact lift_sl2ToP13Gen_relator_eq_one i

/-- The canonical comparison homomorphism from the rank-two braid
presentation into `P13`. -/
noncomputable def sl2ToP13 : SL2P →* P13 :=
  PresentedGroup.toGroup (f := sl2ToP13Gen) fun _ hr =>
    lift_sl2ToP13Gen_eq_one_of_mem hr

@[simp] theorem sl2ToP13_of (i : SL2BraidGenerator) :
    sl2ToP13 (PresentedGroup.of i) = sl2ToP13Gen i :=
  PresentedGroup.toGroup.of _

theorem sl2ToP13_of_zero :
    sl2ToP13 (PresentedGroup.of 0) = x 0 1 :=
  sl2ToP13_of 0

theorem sl2ToP13_of_one :
    sl2ToP13 (PresentedGroup.of 1) = x 2 (-1) :=
  sl2ToP13_of 1

end

end P13SL2Comparison
end GroupApproximation
