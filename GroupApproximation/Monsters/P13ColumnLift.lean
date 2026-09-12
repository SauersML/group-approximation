import GroupApproximation.Monsters.P13WeylFourthPowers
import GroupApproximation.Monsters.P13LowerUnipotentInjectivity

/-!
# The column action of the P13 presentation

The coordinate layer of the completeness programme.  `e3` is the third
standard basis column, `act M v = M.mulVec v` the left action of a
special linear matrix on integer columns, and `act_x0 … act_x5`,
`act_w13`, `act_w23` the explicit coordinate formulas for the images
of the six root elements and the two signed swaps under
`toSL3 : P13 →* SL₃(ℤ)`.  These, with the componentwise
extensionality `vec3_ext`, are what the whole word descent computes
with: `P13DescentCore`, `P13WordDescent`, `P13DescentCases`,
`P13MonomialMachine`, `P13Completeness` and `P13DescentMaster` all run
on them.

Nothing here reduces columns or lifts them.  The containment of the
kernel of `toSL3` in the parabolic subgroup is proved by the word
descent, whose entry point is
`P13DescentMaster.descent_normal_form`.
-/

namespace GroupApproximation
namespace P13ColumnLift

open LiteralP13Presentation P13SteinbergCalculus LiteralP13MatrixModel
open SL3ElementaryGeneration P13UnipotentInjectivity
open P13LowerUnipotentInjectivity
open P13WeylCalculus P13Weyl13Calculus P13Weyl23Calculus

noncomputable section

/-! ## Columns and the matrix action -/

/-- The third standard basis column. -/
def e3 : Fin 3 → ℤ := ![0, 0, 1]

/-- Componentwise extensionality for integer columns. -/
theorem vec3_ext {v w : Fin 3 → ℤ} (h0 : v 0 = w 0) (h1 : v 1 = w 1)
    (h2 : v 2 = w 2) : v = w := by
  funext k
  match k with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1
  | ⟨2, _⟩ => exact h2

/-- The left action of a special linear matrix on integer columns. -/
def act (M : SL3) (v : Fin 3 → ℤ) : Fin 3 → ℤ := M.val.mulVec v

theorem act_apply (M : SL3) (v : Fin 3 → ℤ) (k : Fin 3) :
    act M v k = M.val k 0 * v 0 + M.val k 1 * v 1 + M.val k 2 * v 2 := by
  simp [act, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem act_mul (M N : SL3) (v : Fin 3 → ℤ) :
    act (M * N) v = act M (act N v) := by
  simp [act, Matrix.mulVec_mulVec]

theorem act_one (v : Fin 3 → ℤ) : act 1 v = v := by
  simp [act]

/-! ## The action of the root elements and the signed swaps -/

theorem act_x0 (c : ℤ) (v : Fin 3 → ℤ) :
    act (toSL3 (x 0 c)) v = ![v 0 + c * v 1, v 1, v 2] := by
  have h : toSL3 (x 0 c) = tv 0 1 (by decide) c := by
    rw [toSL3_x, elem0_zpow]
  refine vec3_ext ?_ ?_ ?_ <;>
    simp [h, act_apply, Matrix.transvection, Matrix.single,
      Matrix.add_apply, Matrix.of_apply]

theorem act_x1 (c : ℤ) (v : Fin 3 → ℤ) :
    act (toSL3 (x 1 c)) v = ![v 0 + c * v 2, v 1, v 2] := by
  have h : toSL3 (x 1 c) = tv 0 2 (by decide) c := by
    rw [toSL3_x, elem1_zpow]
  refine vec3_ext ?_ ?_ ?_ <;>
    simp [h, act_apply, Matrix.transvection, Matrix.single,
      Matrix.add_apply, Matrix.of_apply]

theorem act_x2 (c : ℤ) (v : Fin 3 → ℤ) :
    act (toSL3 (x 2 c)) v = ![v 0, v 1 + c * v 0, v 2] := by
  have h : toSL3 (x 2 c) = tv 1 0 (by decide) c := by
    rw [toSL3_x, elem2_zpow]
  refine vec3_ext ?_ ?_ ?_ <;>
    simp [h, act_apply, Matrix.transvection, Matrix.single,
      Matrix.add_apply, Matrix.of_apply]
  ring

theorem act_x3 (c : ℤ) (v : Fin 3 → ℤ) :
    act (toSL3 (x 3 c)) v = ![v 0, v 1 + c * v 2, v 2] := by
  have h : toSL3 (x 3 c) = tv 1 2 (by decide) c := by
    rw [toSL3_x, elem3_zpow]
  refine vec3_ext ?_ ?_ ?_ <;>
    simp [h, act_apply, Matrix.transvection, Matrix.single,
      Matrix.add_apply, Matrix.of_apply]

theorem act_x4 (c : ℤ) (v : Fin 3 → ℤ) :
    act (toSL3 (x 4 c)) v = ![v 0, v 1, v 2 + c * v 0] := by
  have h : toSL3 (x 4 c) = tv 2 0 (by decide) c := by
    rw [toSL3_x, elem4_zpow]
  refine vec3_ext ?_ ?_ ?_ <;>
    simp [h, act_apply, Matrix.transvection, Matrix.single,
      Matrix.add_apply, Matrix.of_apply]
  ring

theorem act_x5 (c : ℤ) (v : Fin 3 → ℤ) :
    act (toSL3 (x 5 c)) v = ![v 0, v 1, v 2 + c * v 1] := by
  have h : toSL3 (x 5 c) = tv 2 1 (by decide) c := by
    rw [toSL3_x, elem5_zpow]
  refine vec3_ext ?_ ?_ ?_ <;>
    simp [h, act_apply, Matrix.transvection, Matrix.single,
      Matrix.add_apply, Matrix.of_apply]
  ring

theorem toSL3_w13 :
    toSL3 w13 = ⟨!![0, 0, 1; 0, 1, 0; -1, 0, 0], by decide⟩ := by
  show toSL3 (x 1 1 * x 4 (-1) * x 1 1) = _
  rw [map_mul, map_mul, toSL3_x, toSL3_x, elem1_zpow, elem4_zpow]
  apply Subtype.ext
  decide

theorem toSL3_w23 :
    toSL3 w23 = ⟨!![1, 0, 0; 0, 0, 1; 0, -1, 0], by decide⟩ := by
  show toSL3 (x 3 1 * x 5 (-1) * x 3 1) = _
  rw [map_mul, map_mul, toSL3_x, toSL3_x, elem3_zpow, elem5_zpow]
  apply Subtype.ext
  decide

theorem act_w13 (v : Fin 3 → ℤ) :
    act (toSL3 w13) v = ![v 2, v 1, -(v 0)] := by
  refine vec3_ext ?_ ?_ ?_ <;> simp [toSL3_w13, act_apply]

theorem act_w23 (v : Fin 3 → ℤ) :
    act (toSL3 w23) v = ![v 0, v 2, -(v 1)] := by
  refine vec3_ext ?_ ?_ ?_ <;> simp [toSL3_w23, act_apply]

end

end P13ColumnLift
end GroupApproximation
