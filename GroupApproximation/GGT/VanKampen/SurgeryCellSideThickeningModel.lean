import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.VecNotation
import GroupApproximation.Meta.AxiomGuard

/-!
# Model test: doubling one relator-face edge across a region side

A model test for `CellSideThickening.CellSideThickeningStatement`
(`SurgeryCellSideThickening.lean`), run before its proof.  The combinatorial map is given by
the edge involution `alpha` and the face permutation, with dart indices in `Fin n`.  Every
claim below is checked by `decide`.

Before the doubling there are twelve darts, six edges `a b c d e f` (`a = 0/1`, `b = 2/3`,
`c = 4/5`, `d = 6/7`, `e = 8/9`, `f = 10/11`), and four vertices.
* The region face `g = [a, b, c, d]` (class `0`).
* The relator face `Π = [ᾱ a, e, ᾱ c, f]` (class `1`).
* A G-face `h = [ᾱ b, ᾱ f]` (class `2`).
* The exterior `[ᾱ d, ᾱ e]` (class `3`).
The vertex count is `4 - 6 + 4 = 2`.  The region `{g}` has boundary cycle `[a, b, c, d]`, with
source arc `[ᾱ a]` on `Π`, right side `[b, c]`, target arc `[d]` on the exterior and an empty
left side.  Its side dart `c` has `Π` across it, so `ᾱ c` is the one cell-side dart.

After doubling `ᾱ c` inside `Π` there are fourteen darts.  The new dart `12` stands in `Π` in
the place of `ᾱ c = 5`.  The new dart `13` and `ᾱ c` form the digon `[13, 5]` (class `4`).
The vertex count is `4 - 7 + 5 = 2`.

* `cellSide_before`: one cell-side dart, and it lies in no arc of the region.
* `cellSide_after`: no cell-side dart, and `c` now has the digon across it.
* `retained`: the old darts other than `ᾱ c` keep their faces and reverses, and `Π` still
  has four darts.
* `boundary_retained`: the boundary darts of the region are the same four darts.
-/

namespace GroupApproximation.GGT.VanKampen.CellSideThickeningModel

/-! ## Before the doubling -/

/-- The edge involution before the doubling. -/
def alphaB : Fin 12 → Fin 12 := ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10]

/-- The face permutation before the doubling. -/
def faceB : Fin 12 → Fin 12 := ![2, 8, 4, 11, 6, 10, 0, 9, 5, 7, 1, 3]

/-- The vertex permutation `faceB ∘ alphaB` before the doubling. -/
def sigmaB : Fin 12 → Fin 12 := ![8, 2, 11, 4, 10, 6, 9, 0, 7, 5, 3, 1]

/-- The faces: `g = 0`, `Π = 1`, `h = 2`, exterior `3`. -/
def faceClassB : Fin 12 → Fin 4 := ![0, 1, 0, 2, 0, 1, 0, 3, 1, 3, 1, 2]

/-- The vertices. -/
def vertexClassB : Fin 12 → Fin 4 := ![0, 1, 1, 2, 2, 3, 3, 0, 0, 3, 2, 1]

theorem map_before :
    (∀ x, alphaB (alphaB x) = x) ∧ (∀ x, alphaB x ≠ x) ∧
      (∀ x, sigmaB x = faceB (alphaB x)) ∧
      (∀ x y, faceB x = faceB y → x = y) ∧
      (∀ x, faceClassB (faceB x) = faceClassB x) ∧
      (∀ x, vertexClassB (sigmaB x) = vertexClassB x) := by
  decide

/-- The four face cycles and four vertex cycles, listed. -/
theorem cycles_before :
    [faceB 0, faceB 2, faceB 4, faceB 6] = [2, 4, 6, 0] ∧
      [faceB 1, faceB 8, faceB 5, faceB 10] = [8, 5, 10, 1] ∧
      [faceB 3, faceB 11] = [11, 3] ∧ [faceB 7, faceB 9] = [9, 7] ∧
      [sigmaB 0, sigmaB 8, sigmaB 7] = [8, 7, 0] ∧ [sigmaB 1, sigmaB 2, sigmaB 11] = [2, 11, 1] ∧
      [sigmaB 3, sigmaB 4, sigmaB 10] = [4, 10, 3] ∧ [sigmaB 5, sigmaB 6, sigmaB 9] = [6, 9, 5] := by
  decide

/-- The side darts, source arc and target arc of the region `{g}`. -/
def sideB : List (Fin 12) := [2, 4]
def sourceB : List (Fin 12) := [1]
def targetB : List (Fin 12) := [6]

/-- **One cell-side dart before the doubling**, the dart `ᾱ c = 5`.  It lies in no arc of the
region, and its face is not in the region. -/
theorem cellSide_before :
    (Finset.univ.filter fun x : Fin 12 => faceClassB x = 1 ∧ alphaB x ∈ sideB).card = 1 ∧
      faceClassB 5 = 1 ∧ alphaB 5 ∈ sideB ∧ (5 : Fin 12) ∉ sourceB ∧ (5 : Fin 12) ∉ targetB ∧
      faceClassB 1 = 1 ∧ faceClassB (alphaB 6) = 3 := by
  decide

/-! ## After the doubling -/

/-- The edge involution after the doubling. -/
def alphaA : Fin 14 → Fin 14 := ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12]

/-- The face permutation after the doubling. -/
def faceA : Fin 14 → Fin 14 := ![2, 8, 4, 11, 6, 13, 0, 9, 12, 7, 1, 3, 10, 5]

/-- The vertex permutation `faceA ∘ alphaA` after the doubling. -/
def sigmaA : Fin 14 → Fin 14 := ![8, 2, 11, 4, 13, 6, 9, 0, 7, 12, 3, 1, 5, 10]

/-- The faces: `g = 0`, `Π = 1`, `h = 2`, exterior `3`, digon `4`. -/
def faceClassA : Fin 14 → Fin 5 := ![0, 1, 0, 2, 0, 4, 0, 3, 1, 3, 1, 2, 1, 4]

/-- The vertices. -/
def vertexClassA : Fin 14 → Fin 4 := ![0, 1, 1, 2, 2, 3, 3, 0, 0, 3, 2, 1, 3, 2]

theorem map_after :
    (∀ x, alphaA (alphaA x) = x) ∧ (∀ x, alphaA x ≠ x) ∧
      (∀ x, sigmaA x = faceA (alphaA x)) ∧
      (∀ x y, faceA x = faceA y → x = y) ∧
      (∀ x, faceClassA (faceA x) = faceClassA x) ∧
      (∀ x, vertexClassA (sigmaA x) = vertexClassA x) := by
  decide

/-- The five face cycles and four vertex cycles, listed. -/
theorem cycles_after :
    [faceA 0, faceA 2, faceA 4, faceA 6] = [2, 4, 6, 0] ∧
      [faceA 1, faceA 8, faceA 12, faceA 10] = [8, 12, 10, 1] ∧
      [faceA 3, faceA 11] = [11, 3] ∧ [faceA 7, faceA 9] = [9, 7] ∧ [faceA 13, faceA 5] = [5, 13] ∧
      [sigmaA 0, sigmaA 8, sigmaA 7] = [8, 7, 0] ∧ [sigmaA 1, sigmaA 2, sigmaA 11] = [2, 11, 1] ∧
      [sigmaA 3, sigmaA 4, sigmaA 13, sigmaA 10] = [4, 13, 10, 3] ∧
      [sigmaA 5, sigmaA 6, sigmaA 9, sigmaA 12] = [6, 9, 12, 5] := by
  decide

/-- The side darts of the region `{g}` after the doubling. -/
def sideA : List (Fin 14) := [2, 4]

/-- **No cell-side dart after the doubling**, and the side dart `c` has the digon across it. -/
theorem cellSide_after :
    (Finset.univ.filter fun x : Fin 14 => faceClassA x = 1 ∧ alphaA x ∈ sideA).card = 0 ∧
      faceClassA (alphaA 4) = 4 ∧ faceClassA 12 = 1 ∧ faceClassA (alphaA 12) = 4 := by
  decide

/-- The old darts other than `ᾱ c` keep their faces, every old dart keeps its reverse, and `Π`
still has four darts. -/
theorem retained :
    (∀ x : Fin 12, x ≠ 5 →
      (faceClassA (Fin.castLE (by decide) x)).val = (faceClassB x).val) ∧
      (∀ x : Fin 12, alphaA (Fin.castLE (by decide) x) = Fin.castLE (by decide) (alphaB x)) ∧
      (Finset.univ.filter fun x : Fin 12 => faceClassB x = 1).card = 4 ∧
      (Finset.univ.filter fun x : Fin 14 => faceClassA x = 1).card = 4 := by
  decide

/-- The boundary darts of the region `{g}` are the same four darts before and after. -/
theorem boundary_retained :
    (Finset.univ.filter fun x : Fin 12 => faceClassB x = 0 ∧ faceClassB (alphaB x) ≠ 0) =
        {0, 2, 4, 6} ∧
      (Finset.univ.filter fun x : Fin 14 => faceClassA x = 0 ∧ faceClassA (alphaA x) ≠ 0) =
        {0, 2, 4, 6} := by
  decide

end GroupApproximation.GGT.VanKampen.CellSideThickeningModel

#audit_axioms GroupApproximation.GGT.VanKampen.CellSideThickeningModel.map_before
#audit_axioms GroupApproximation.GGT.VanKampen.CellSideThickeningModel.cycles_before
#audit_axioms GroupApproximation.GGT.VanKampen.CellSideThickeningModel.cellSide_before
#audit_axioms GroupApproximation.GGT.VanKampen.CellSideThickeningModel.map_after
#audit_axioms GroupApproximation.GGT.VanKampen.CellSideThickeningModel.cycles_after
#audit_axioms GroupApproximation.GGT.VanKampen.CellSideThickeningModel.cellSide_after
#audit_axioms GroupApproximation.GGT.VanKampen.CellSideThickeningModel.retained
#audit_axioms GroupApproximation.GGT.VanKampen.CellSideThickeningModel.boundary_retained
