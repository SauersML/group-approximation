import GroupApproximation.Monsters.P13WeylFourthPowers
import GroupApproximation.Monsters.P13BlockSL2

/-!
# All three block pairs of P13 are faithful copies of `SL₂(ℤ)`

Each block pair of `P13` satisfies the braid relation and the
fourth-power relation (`P13WeylFourthPowers`), so the rank-two braid
presentation maps into `P13` three ways:

* `a ↦ x₁₂(1), b ↦ x₂₁(-1)` (`P13SL2Comparison`),
* `a ↦ x₂₃(1), b ↦ x₃₂(-1)` (this file),
* `a ↦ x₁₃(1), b ↦ x₃₁(-1)` (this file).

Composing with the matrix model realizes the corresponding block
embeddings of `SL₂(ℤ)` into `SL₃(ℤ)`, and rank-two completeness makes
all three comparisons injective: every block pair generates a faithful
copy of `SL₂(ℤ)` inside `P13`.
-/

namespace GroupApproximation
namespace P13SL2ComparisonAll

open LiteralP13Presentation LiteralP13MatrixModel P13SteinbergCalculus
open P13WeylCalculus P13Weyl23Calculus P13Weyl13Calculus
open P13WeylFourthPowers SL2BraidPresentation PresentedGroupRelatorReplay
open P13UnipotentInjectivity

noncomputable section

/-! ## The 23-block comparison -/

/-- The generator assignment `a ↦ x₂₃(1)`, `b ↦ x₃₂(-1)`. -/
def gen23 : Fin 2 → P13
  | 0 => x 3 1
  | 1 => x 5 (-1)

private theorem lift23_relator_zero :
    FreeGroup.lift gen23 (sl2Relator 0) = 1 := by
  have hb : (x 3 1 : P13) * x 5 (-1) * x 3 1 *
      (x 5 (-1) * x 3 1 * x 5 (-1))⁻¹ = 1 := by
    rw [braid23]
    group
  calc FreeGroup.lift gen23 (sl2Relator 0)
      = x 3 1 * x 5 (-1) * x 3 1 *
        (x 5 (-1) * x 3 1 * x 5 (-1))⁻¹ := by
        simp only [sl2Relator, sl2RelatorLetters, word, FreeGroup.lift_mk,
          List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          cond_true, cond_false, gen23]
        group
    _ = 1 := hb

private theorem lift23_relator_one :
    FreeGroup.lift gen23 (sl2Relator 1) = 1 := by
  have h4 : (x 3 1 : P13) * x 5 (-1) * x 3 1 *
      (x 3 1 * x 5 (-1) * x 3 1) * (x 3 1 * x 5 (-1) * x 3 1) *
      (x 3 1 * x 5 (-1) * x 3 1) = 1 := w23_pow_four
  calc FreeGroup.lift gen23 (sl2Relator 1)
      = x 3 1 * x 5 (-1) * x 3 1 *
        (x 3 1 * x 5 (-1) * x 3 1) * (x 3 1 * x 5 (-1) * x 3 1) *
        (x 3 1 * x 5 (-1) * x 3 1) := by
        simp only [sl2Relator, sl2RelatorLetters, word, FreeGroup.lift_mk,
          List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          cond_true, gen23]
        group
    _ = 1 := h4

theorem lift_gen23_eq_one_of_mem {r : FreeGroup SL2BraidGenerator}
    (hr : r ∈ (sl2Relators : Set (FreeGroup SL2BraidGenerator))) :
    FreeGroup.lift gen23 r = 1 := by
  obtain ⟨i, rfl⟩ := (mem_sl2Relators_iff r).mp hr
  fin_cases i
  · exact lift23_relator_zero
  · exact lift23_relator_one

/-- The 23-block comparison homomorphism. -/
noncomputable def sl2ToP13Block23 : SL2P →* P13 :=
  PresentedGroup.toGroup (f := gen23) fun _ hr =>
    lift_gen23_eq_one_of_mem hr

@[simp] theorem sl2ToP13Block23_of (i : SL2BraidGenerator) :
    sl2ToP13Block23 (PresentedGroup.of i) = gen23 i :=
  PresentedGroup.toGroup.of _

/-! ## The 13-block comparison -/

/-- The generator assignment `a ↦ x₁₃(1)`, `b ↦ x₃₁(-1)`. -/
def gen13 : Fin 2 → P13
  | 0 => x 1 1
  | 1 => x 4 (-1)

private theorem lift13_relator_zero :
    FreeGroup.lift gen13 (sl2Relator 0) = 1 := by
  have hb : (x 1 1 : P13) * x 4 (-1) * x 1 1 *
      (x 4 (-1) * x 1 1 * x 4 (-1))⁻¹ = 1 := by
    rw [braid13]
    group
  calc FreeGroup.lift gen13 (sl2Relator 0)
      = x 1 1 * x 4 (-1) * x 1 1 *
        (x 4 (-1) * x 1 1 * x 4 (-1))⁻¹ := by
        simp only [sl2Relator, sl2RelatorLetters, word, FreeGroup.lift_mk,
          List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          cond_true, cond_false, gen13]
        group
    _ = 1 := hb

private theorem lift13_relator_one :
    FreeGroup.lift gen13 (sl2Relator 1) = 1 := by
  have h4 : (x 1 1 : P13) * x 4 (-1) * x 1 1 *
      (x 1 1 * x 4 (-1) * x 1 1) * (x 1 1 * x 4 (-1) * x 1 1) *
      (x 1 1 * x 4 (-1) * x 1 1) = 1 := w13_pow_four
  calc FreeGroup.lift gen13 (sl2Relator 1)
      = x 1 1 * x 4 (-1) * x 1 1 *
        (x 1 1 * x 4 (-1) * x 1 1) * (x 1 1 * x 4 (-1) * x 1 1) *
        (x 1 1 * x 4 (-1) * x 1 1) := by
        simp only [sl2Relator, sl2RelatorLetters, word, FreeGroup.lift_mk,
          List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          cond_true, gen13]
        group
    _ = 1 := h4

theorem lift_gen13_eq_one_of_mem {r : FreeGroup SL2BraidGenerator}
    (hr : r ∈ (sl2Relators : Set (FreeGroup SL2BraidGenerator))) :
    FreeGroup.lift gen13 r = 1 := by
  obtain ⟨i, rfl⟩ := (mem_sl2Relators_iff r).mp hr
  fin_cases i
  · exact lift13_relator_zero
  · exact lift13_relator_one

/-- The 13-block comparison homomorphism. -/
noncomputable def sl2ToP13Block13 : SL2P →* P13 :=
  PresentedGroup.toGroup (f := gen13) fun _ hr =>
    lift_gen13_eq_one_of_mem hr

@[simp] theorem sl2ToP13Block13_of (i : SL2BraidGenerator) :
    sl2ToP13Block13 (PresentedGroup.of i) = gen13 i :=
  PresentedGroup.toGroup.of _

end

end P13SL2ComparisonAll
end GroupApproximation
