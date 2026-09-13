import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.VecNotation
import GroupApproximation.Meta.AxiomGuard

/-!
# Model test: doubling an edge between two regions

A model test for the region-pair thickening (`SurgeryRegionPairThickening.lean`), run before its
proof.  The edge condition `regions` of `PocketWalk.CopyClean` and `CellPocketWalk.CopyClean` asks
that no edge join a face of one selected region to a face of another.  Doubling such an edge inside
the face of one region (`FaceEdgeDoubling.diagram`) puts a G-cell digon between them.  The
combinatorial map is given by the edge involution `alpha` and the face permutation, with dart
indices in `Fin n`, and the vertex permutation is `face ∘ alpha`.  Every claim below is checked by
`decide`.

## Before the doubling

Six darts on three edges `{0,1}`, `{2,3}`, `{4,5}` from `u` to `v`.  The face `A = [0, 3]` of the
region `x` (class `0`), the face `B = [4, 1]` of the region `y` (class `1`) and the exterior
`O = [2, 5]` (class `2`).  The vertex count is `2 - 3 + 3 = 2`.  The darts `0` and `1` of the shared
edge are region-pair darts.  The boundary darts of `A` are `0` and `3`, and those of `B` are `1`
and `4`.

## After doubling `0` inside `A`

Eight darts.  The new dart `6` stands in `A` in the place of `0`, and `0` and `7 = α 6` form the
digon `[0, 7]` (class `3`).  The vertex count is `2 - 4 + 4 = 2`.
* No region-pair dart remains.
* The boundary darts of `A` are `3` and `6`: the old ones with `0` replaced by the new dart, as
  through `FaceEdgeDoubling.dartImage`.
* The boundary darts of `B` are unchanged.

## Calibration: the digon inside `A`

Counting the digon as a face of `x` (the collar face set) keeps the region-pair darts `0` and `1`.
So the separating copy must leave the digon out of both regions, and the region holding the doubled
face changes by a dart substitution.

* `map_before`, `cycles_before`, `pair_before`, `boundary_before`.
* `map_after`, `cycles_after`, `pair_after`, `boundary_after`, `retained`, `collar_keeps_pair`.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 2121, "Hull's small cancellation theorem",
through Osin's Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.RegionPairThickeningModel

/-! ## Before the doubling -/

/-- The edge involution before the doubling. -/
def alphaB : Fin 6 → Fin 6 := ![1, 0, 3, 2, 5, 4]

/-- The face permutation before the doubling. -/
def faceB : Fin 6 → Fin 6 := ![3, 4, 5, 0, 1, 2]

/-- The vertex permutation `faceB ∘ alphaB` before the doubling. -/
def sigmaB : Fin 6 → Fin 6 := ![4, 3, 0, 5, 2, 1]

/-- The faces: `A = 0` (region `x`), `B = 1` (region `y`), exterior `2`. -/
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

/-- The three face cycles and the two vertex cycles, listed. -/
theorem cycles_before :
    [faceB 0, faceB 3] = [3, 0] ∧ [faceB 4, faceB 1] = [1, 4] ∧ [faceB 2, faceB 5] = [5, 2] ∧
      [sigmaB 0, sigmaB 4, sigmaB 2] = [4, 2, 0] ∧ [sigmaB 1, sigmaB 3, sigmaB 5] = [3, 5, 1] := by
  decide

/-- **Two region-pair darts before the doubling**, the darts `0` and `1` of the shared edge, and
`A` has two darts. -/
theorem pair_before :
    (Finset.univ.filter fun x : Fin 6 =>
        (faceClassB x = 0 ∧ faceClassB (alphaB x) = 1) ∨
          (faceClassB x = 1 ∧ faceClassB (alphaB x) = 0)).card = 2 ∧
      faceClassB 0 = 0 ∧ faceClassB (alphaB 0) = 1 ∧
      (Finset.univ.filter fun x : Fin 6 => faceClassB x = 0).card = 2 := by
  decide

/-- The boundary darts of `A` are `0` and `3`; those of `B` are `1` and `4`. -/
theorem boundary_before :
    (Finset.univ.filter fun x : Fin 6 => faceClassB x = 0 ∧ faceClassB (alphaB x) ≠ 0) =
        {0, 3} ∧
      (Finset.univ.filter fun x : Fin 6 => faceClassB x = 1 ∧ faceClassB (alphaB x) ≠ 1) =
        {1, 4} := by
  decide

/-! ## After doubling `0` inside `A` -/

/-- The edge involution after the doubling. -/
def alphaA : Fin 8 → Fin 8 := ![1, 0, 3, 2, 5, 4, 7, 6]

/-- The face permutation after the doubling. -/
def faceA : Fin 8 → Fin 8 := ![7, 4, 5, 6, 1, 2, 3, 0]

/-- The vertex permutation `faceA ∘ alphaA` after the doubling. -/
def sigmaA : Fin 8 → Fin 8 := ![4, 7, 6, 5, 2, 1, 0, 3]

/-- The faces: `A = 0`, `B = 1`, exterior `2`, digon `3`. -/
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

/-- The four face cycles and the two vertex cycles, listed. -/
theorem cycles_after :
    [faceA 3, faceA 6] = [6, 3] ∧ [faceA 4, faceA 1] = [1, 4] ∧ [faceA 2, faceA 5] = [5, 2] ∧
      [faceA 0, faceA 7] = [7, 0] ∧
      [sigmaA 0, sigmaA 4, sigmaA 2, sigmaA 6] = [4, 2, 6, 0] ∧
      [sigmaA 1, sigmaA 7, sigmaA 3, sigmaA 5] = [7, 3, 5, 1] := by
  decide

/-- **No region-pair dart after the doubling**: the new dart `6` of `A` and the old dart `1` of
`B` both have the digon across them. -/
theorem pair_after :
    (Finset.univ.filter fun x : Fin 8 =>
        (faceClassA x = 0 ∧ faceClassA (alphaA x) = 1) ∨
          (faceClassA x = 1 ∧ faceClassA (alphaA x) = 0)).card = 0 ∧
      faceClassA 6 = 0 ∧ faceClassA (alphaA 6) = 3 ∧
      faceClassA 1 = 1 ∧ faceClassA (alphaA 1) = 3 := by
  decide

/-- **The boundary of `A` is the old one with `0` replaced by the new dart `6`**; the boundary of
`B` is unchanged. -/
theorem boundary_after :
    (Finset.univ.filter fun x : Fin 8 => faceClassA x = 0 ∧ faceClassA (alphaA x) ≠ 0) =
        {3, 6} ∧
      (Finset.univ.filter fun x : Fin 8 => faceClassA x = 1 ∧ faceClassA (alphaA x) ≠ 1) =
        {1, 4} := by
  decide

/-- The old darts keep their reverses, the old darts other than `0` keep their faces, `0` moves
to the digon, and `A` still has two darts. -/
theorem retained :
    (∀ x : Fin 6, (alphaA (Fin.castLE (by decide) x)).val = (alphaB x).val) ∧
      (∀ x : Fin 6, x ≠ 0 →
        (faceClassA (Fin.castLE (by decide) x)).val = (faceClassB x).val) ∧
      faceClassA 0 = 3 ∧
      (Finset.univ.filter fun x : Fin 8 => faceClassA x = 0).card = 2 := by
  decide

/-- **Calibration: the digon counted inside `A` keeps the region-pair darts** `0` and `1`. -/
theorem collar_keeps_pair :
    (Finset.univ.filter fun x : Fin 8 =>
        ((faceClassA x = 0 ∨ faceClassA x = 3) ∧ faceClassA (alphaA x) = 1) ∨
          (faceClassA x = 1 ∧ (faceClassA (alphaA x) = 0 ∨ faceClassA (alphaA x) = 3))).card =
      2 := by
  decide

end GroupApproximation.GGT.VanKampen.RegionPairThickeningModel

#audit_axioms GroupApproximation.GGT.VanKampen.RegionPairThickeningModel.pair_after
#audit_axioms GroupApproximation.GGT.VanKampen.RegionPairThickeningModel.boundary_after
#audit_axioms GroupApproximation.GGT.VanKampen.RegionPairThickeningModel.collar_keeps_pair
