import GroupApproximation.BooneHigman.V.Group
import GroupApproximation.Leavitt.FamilyVEmbedding

/-!
# The binary case agrees with the development's Thompson group `V`

`Leavitt/ThompsonV.lean` defines Thompson's group `V` on `ThompsonV.Boundary = ℕ → Fin 2` as the closure of the
tree-table bijections, and `Leavitt/FamilyVEmbedding.lean` proves it lies in the depth group
`ThompsonV.tableGroup`.  The arity-general definitions of `BooneHigman.V` specialize at `X = Fin 2` to exactly
those binary definitions, so `higmanThompsonV (Fin 2)` is `ThompsonV.tableGroup` and contains `ThompsonV.thompsonV`.
-/

namespace GroupApproximation
namespace BooneHigman

theorem thompsonV_prepend_eq (w : List (Fin 2)) (x : Cantor (Fin 2)) :
    ThompsonV.prepend w x = prepend w x := rfl

theorem thompsonV_hasDepth_iff (f : Equiv.Perm (Cantor (Fin 2))) (N : ℕ) :
    ThompsonV.HasDepth f N ↔ HasDepth f N := Iff.rfl

/-- The binary depth group of the development is `V_2`. -/
theorem tableGroup_eq_higmanThompsonV : ThompsonV.tableGroup = higmanThompsonV (Fin 2) := by
  ext f
  exact Iff.rfl

/-- The development's Thompson group `V`, the closure of the tree tables, lies in `V_2`. -/
theorem thompsonV_le_higmanThompsonV : ThompsonV.thompsonV ≤ higmanThompsonV (Fin 2) := by
  rw [← tableGroup_eq_higmanThompsonV]
  exact ThompsonV.thompsonV_le_tableGroup

end BooneHigman
end GroupApproximation
