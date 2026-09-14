import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.VecNotation
import GroupApproximation.Meta.AxiomGuard

/-!
# Model test: doubling an edge between two regions

A model test for the side–side thickening (`SurgerySideSideThickening.lean`), run before its
proof.  The edge condition `CellPocketWalk.CopyClean.regions` (`Estimating/OsinPocketCellCopyWalk.lean`)
asks that no edge join a face of the region `a` to a face of the region `b`.  The doubling of
`FaceEdgeDoubling` along such an edge, inside the face of `a`, puts a G-cell digon between the two
regions, and the digon lies in neither.  The combinatorial map is given by the edge involution
`alpha` and the face permutation, with dart indices in `Fin n`, and the vertex permutation is
`face ∘ alpha`.  Every claim below is checked by `decide`.

A **side–side dart** is a dart on a face of one region whose reverse lies on a face of the other.

Before the doubling there are six darts on three edges `{0,1}`, `{2,3}`, `{4,5}` from `u` to `v`.
The face `g_a = [0, 3]` (class `0`) is the region `a`, the face `g_b = [4, 1]` (class `1`) is the
region `b`, and the exterior is `[2, 5]` (class `2`).  The vertex count is `2 - 3 + 3 = 2`.  The
darts `0` and `1` of the shared edge are side–side darts.  The boundary darts of `a` are `{0, 3}`,
and those of `b` are `{4, 1}`.

After doubling `0` inside `g_a` there are eight darts.  The new dart `6` stands in `g_a` in the
place of `0`, and `0` and `7 = ᾱ 6` form the digon `[0, 7]` (class `3`).  The vertex count is
`2 - 4 + 4 = 2`.  No side–side dart remains.  The boundary darts of `a` are `{6, 3}`, the old ones
with `0` replaced by the new dart, and those of `b` are the same `{4, 1}`.

* `map_before`, `cycles_before`, `sideSide_before`, `boundary_before`.
* `map_after`, `cycles_after`, `sideSide_after`, `boundary_after`, `retained`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.SideSideThickeningModel

/-! ## Before the doubling -/

/-- The edge involution before the doubling. -/
def alphaB : Fin 6 → Fin 6 := ![1, 0, 3, 2, 5, 4]

/-- The face permutation before the doubling. -/
def faceB : Fin 6 → Fin 6 := ![3, 4, 5, 0, 1, 2]

/-- The vertex permutation `faceB ∘ alphaB` before the doubling. -/
def sigmaB : Fin 6 → Fin 6 := ![4, 3, 0, 5, 2, 1]

/-- The faces: `g_a = 0`, `g_b = 1`, exterior `2`. -/
def faceClassB : Fin 6 → Fin 3 := ![0, 1, 2, 0, 1, 2]

/-- The vertices: `u = 0`, `v = 1`. -/
def vertexClassB : Fin 6 → Fin 2 := ![0, 1, 0, 1, 0, 1]

theorem map_before :
    (∀ x, alphaB (alphaB x) = x) ∧ (∀ x, alphaB x ≠ x) ∧
      (∀ x, sigmaB x = faceB (alphaB x)) ∧
      (∀ x y, faceB x = faceB y → x = y) ∧
      (∀ x, faceClassB (faceB x) = faceClassB x) ∧
      (∀ x, vertexClassB (sigmaB x) = vertexClassB x) := by
  decide

/-- The three face cycles and two vertex cycles, listed. -/
theorem cycles_before :
    [faceB 0, faceB 3] = [3, 0] ∧ [faceB 4, faceB 1] = [1, 4] ∧ [faceB 2, faceB 5] = [5, 2] ∧
      [sigmaB 0, sigmaB 4, sigmaB 2] = [4, 2, 0] ∧ [sigmaB 1, sigmaB 3, sigmaB 5] = [3, 5, 1] := by
  decide

/-- **Two side–side darts before the doubling**, the darts `0` and `1` of the shared edge. -/
theorem sideSide_before :
    (Finset.univ.filter fun x : Fin 6 =>
        (faceClassB x = 0 ∧ faceClassB (alphaB x) = 1) ∨
          (faceClassB x = 1 ∧ faceClassB (alphaB x) = 0)).card = 2 ∧
      faceClassB 0 = 0 ∧ faceClassB (alphaB 0) = 1 := by
  decide

/-- The boundary darts of the two regions before the doubling. -/
theorem boundary_before :
    (Finset.univ.filter fun x : Fin 6 => faceClassB x = 0 ∧ faceClassB (alphaB x) ≠ 0) =
        {0, 3} ∧
      (Finset.univ.filter fun x : Fin 6 => faceClassB x = 1 ∧ faceClassB (alphaB x) ≠ 1) =
        {1, 4} := by
  decide

/-! ## After the doubling -/

/-- The edge involution after the doubling. -/
def alphaA : Fin 8 → Fin 8 := ![1, 0, 3, 2, 5, 4, 7, 6]

/-- The face permutation after the doubling. -/
def faceA : Fin 8 → Fin 8 := ![7, 4, 5, 6, 1, 2, 3, 0]

/-- The vertex permutation `faceA ∘ alphaA` after the doubling. -/
def sigmaA : Fin 8 → Fin 8 := ![4, 7, 6, 5, 2, 1, 0, 3]

/-- The faces: `g_a = 0`, `g_b = 1`, exterior `2`, digon `3`. -/
def faceClassA : Fin 8 → Fin 4 := ![3, 1, 2, 0, 1, 2, 0, 3]

/-- The vertices: `u = 0`, `v = 1`. -/
def vertexClassA : Fin 8 → Fin 2 := ![0, 1, 0, 1, 0, 1, 0, 1]

theorem map_after :
    (∀ x, alphaA (alphaA x) = x) ∧ (∀ x, alphaA x ≠ x) ∧
      (∀ x, sigmaA x = faceA (alphaA x)) ∧
      (∀ x y, faceA x = faceA y → x = y) ∧
      (∀ x, faceClassA (faceA x) = faceClassA x) ∧
      (∀ x, vertexClassA (sigmaA x) = vertexClassA x) := by
  decide

/-- The four face cycles and two vertex cycles, listed. -/
theorem cycles_after :
    [faceA 6, faceA 3] = [3, 6] ∧ [faceA 4, faceA 1] = [1, 4] ∧ [faceA 2, faceA 5] = [5, 2] ∧
      [faceA 0, faceA 7] = [7, 0] ∧
      [sigmaA 0, sigmaA 4, sigmaA 2, sigmaA 6] = [4, 2, 6, 0] ∧
      [sigmaA 1, sigmaA 7, sigmaA 3, sigmaA 5] = [7, 3, 5, 1] := by
  decide

/-- **No side–side dart after the doubling**: the new dart `6` of `g_a` and the old dart `1` of
`g_b` both have the digon across them. -/
theorem sideSide_after :
    (Finset.univ.filter fun x : Fin 8 =>
        (faceClassA x = 0 ∧ faceClassA (alphaA x) = 1) ∨
          (faceClassA x = 1 ∧ faceClassA (alphaA x) = 0)).card = 0 ∧
      faceClassA (alphaA 6) = 3 ∧ faceClassA (alphaA 1) = 3 := by
  decide

/-- The boundary darts of `a` are the old ones with `0` replaced by the new dart `6`, and those of
`b` are unchanged. -/
theorem boundary_after :
    (Finset.univ.filter fun x : Fin 8 => faceClassA x = 0 ∧ faceClassA (alphaA x) ≠ 0) =
        {3, 6} ∧
      (Finset.univ.filter fun x : Fin 8 => faceClassA x = 1 ∧ faceClassA (alphaA x) ≠ 1) =
        {1, 4} := by
  decide

/-- The old darts other than `0` keep their faces and every old dart keeps its reverse. -/
theorem retained :
    (∀ x : Fin 6, x ≠ 0 →
      (faceClassA (Fin.castLE (by decide) x)).val = (faceClassB x).val) ∧
      (∀ x : Fin 6,
        alphaA (Fin.castLE (by decide) x) = Fin.castLE (by decide) (alphaB x)) := by
  decide

end GroupApproximation.GGT.VanKampen.SideSideThickeningModel

#audit_axioms GroupApproximation.GGT.VanKampen.SideSideThickeningModel.map_before
#audit_axioms GroupApproximation.GGT.VanKampen.SideSideThickeningModel.cycles_before
#audit_axioms GroupApproximation.GGT.VanKampen.SideSideThickeningModel.sideSide_before
#audit_axioms GroupApproximation.GGT.VanKampen.SideSideThickeningModel.boundary_before
#audit_axioms GroupApproximation.GGT.VanKampen.SideSideThickeningModel.map_after
#audit_axioms GroupApproximation.GGT.VanKampen.SideSideThickeningModel.cycles_after
#audit_axioms GroupApproximation.GGT.VanKampen.SideSideThickeningModel.sideSide_after
#audit_axioms GroupApproximation.GGT.VanKampen.SideSideThickeningModel.boundary_after
#audit_axioms GroupApproximation.GGT.VanKampen.SideSideThickeningModel.retained
