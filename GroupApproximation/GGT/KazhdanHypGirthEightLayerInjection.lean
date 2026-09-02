import GroupApproximation.GGT.KazhdanHypGirthEightVKInterface
import GroupApproximation.GGT.VanKampen.DiscDiagram
import GroupApproximation.GGT.VanKampen.CombMapStars

/-!
# Incidences in successive face-star layers

This is the clean layer-injection module for the girth-eight construction.
It deliberately does not import `KazhdanHypGirthEightPrimitives2`: the
interface below is the part needed by that module, while its larger import
closure is currently under repair.

For a centered boundary window, `CenteredWindowFirstLayerIncidence` records
the first inner face reached at each surviving position and the fact that the
position occurs on that face.  `firstLayerIncidenceIndex` reads the position
back from the duplicate-free face boundary, and `firstLayerIncidenceSlot`
places that index in the uniform perimeter range.  The resulting
`LayerIncidenceInjection` gives the exact numerical consequence consumed by
the successive-star estimate.

The face families are defined directly from `CombMap.faceStarLayer`; their
pairwise disjointness is proved from the named `CombMap.faceStarLayer_disjoint`
theorem.  The one-triangle model at the end tests the generic injection and
its unit covering inequality without importing the red higher-level module.
-/

namespace GroupApproximation
namespace GGT
namespace GirthEightPrimitives2

open GroupApproximation.KazhdanHyp
open GirthEightVKInterface
open GroupApproximation.GGT.VanKampen
open scoped BigOperators

section Table

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]
  {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}

/-! ## The face families -/

/-- Faces incident to the vertices of the selected outer-boundary subpath. -/
noncomputable def boundaryFaceSeed
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) : Finset Delta.toCombMap.Face := by
  classical
  exact P.darts.toFinset.biUnion fun dart ↦
    Delta.toCombMap.faceStar (Delta.toCombMap.faceOf dart)

/-- The faces first reached at radius `n` from the centered boundary seed. -/
noncomputable def boundaryFaceStarLayer
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (n : ℕ) : Finset Delta.toCombMap.Face :=
  Delta.toCombMap.faceStarLayer (boundaryFaceSeed Delta P) n

/-- The inner faces in one boundary-star layer. -/
noncomputable def innerBoundaryFaceStarLayer
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (n : ℕ) : Finset Delta.toCombMap.Face := by
  classical
  exact boundaryFaceStarLayer Delta P n ∩ Delta.innerFaces

omit [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
/-- Intersecting with inner faces preserves disjointness of the star layers. -/
theorem innerBoundaryFaceStarLayer_disjoint
    (Delta : VanKampen.DiscDiagram (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (innerBoundaryFaceStarLayer Delta P i)
      (innerBoundaryFaceStarLayer Delta P j) := by
  classical
  exact (VanKampen.CombMap.faceStarLayer_disjoint Delta.toCombMap
    (boundaryFaceSeed Delta P) hij).mono
    Finset.inter_subset_left Finset.inter_subset_left

/-! ## Face positions and incidence slots -/

/-- A layer injection assigns every surviving window position to a face and
one of a uniformly bounded number of incidences on that face. -/
structure LayerIncidenceInjection
    {Face : Type}
    (layer : Fin depth → Finset Face) (scale loss perimeter : ℕ) where
  /-- The selected face and incidence slot for a surviving position. -/
  encode : ∀ i : Fin depth,
    Fin (scale - loss) → {face // face ∈ (layer i : Set Face)} × Fin perimeter
  /-- Positions in one layer have distinct face-incidence pairs. -/
  injective : ∀ i : Fin depth, Function.Injective (encode i)

/-- Geometric data saying that every surviving position has a first face in
the indicated inner star layer.  The incidence slot is reconstructed from
the stored face boundary, rather than supplied as an opaque choice. -/
structure CenteredWindowFirstLayerIncidence
    (Delta : VanKampen.DiscDiagram (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (depth scale loss perimeter : ℕ) where
  /-- The surviving position as an occurrence in the boundary subpath. -/
  position : ∀ _i : Fin depth, Fin (scale - loss) → Fin P.darts.length
  /-- Positions in one layer are distinct boundary occurrences. -/
  position_injective : ∀ i : Fin depth, Function.Injective (position i)
  /-- First inner layer face met by a surviving position. -/
  face : ∀ _i : Fin depth, Fin (scale - loss) → Delta.toCombMap.Face
  /-- The selected face belongs to the required inner layer. -/
  face_mem : ∀ (i : Fin depth) (q : Fin (scale - loss)),
    face i q ∈ innerBoundaryFaceStarLayer Delta P (i : ℕ)
  /-- The boundary dart at the position occurs on the selected face. -/
  on_face : ∀ (i : Fin depth) (q : Fin (scale - loss)),
    P.darts.get (position i q) ∈
      (Delta.faceBoundary (face i q)).darts
  /-- Every selected face has at most the prescribed perimeter. -/
  faceDegree_le : ∀ (i : Fin depth) (q : Fin (scale - loss)),
    Delta.toCombMap.faceDegree (face i q) ≤ perimeter

omit [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
/-- A literal boundary subpath has no repeated darts. -/
theorem boundarySubpath_nodup
    (Delta : VanKampen.DiscDiagram (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) : P.darts.Nodup := by
  have hall :
      (P.beforeDarts ++ (P.darts ++ P.afterDarts)).Nodup := by
    rw [← List.append_assoc, ← P.split]
    exact (Delta.faceBoundary Delta.outerFace).nodup
  exact hall.of_append_right.of_append_left

/-- The unique incidence index of the selected boundary dart in its face
boundary. -/
noncomputable def firstLayerIncidenceIndex
    (Delta : VanKampen.DiscDiagram (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (depth scale loss perimeter : ℕ)
    (C : CenteredWindowFirstLayerIncidence Delta P depth scale loss perimeter)
    (i : Fin depth) (q : Fin (scale - loss)) :
    Fin (Delta.faceBoundary (C.face i q)).darts.length := by
  classical
  exact ((Delta.faceBoundary (C.face i q)).nodup.getEquiv
    (Delta.faceBoundary (C.face i q)).darts).symm
      ⟨P.darts.get (C.position i q), C.on_face i q⟩

omit [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
/-- Reading the incidence index returns the selected boundary dart. -/
theorem firstLayerIncidenceIndex_get
    (Delta : VanKampen.DiscDiagram (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (depth scale loss perimeter : ℕ)
    (C : CenteredWindowFirstLayerIncidence Delta P depth scale loss perimeter)
    (i : Fin depth) (q : Fin (scale - loss)) :
    (Delta.faceBoundary (C.face i q)).darts.get
        (firstLayerIncidenceIndex Delta P depth scale loss perimeter C i q) =
      P.darts.get (C.position i q) := by
  classical
  have h := ((Delta.faceBoundary (C.face i q)).nodup.getEquiv
      (Delta.faceBoundary (C.face i q)).darts).apply_symm_apply
      ⟨P.darts.get (C.position i q), C.on_face i q⟩
  exact congrArg Subtype.val h

/-- Convert a face-boundary incidence index into a slot in the uniform
perimeter range. -/
noncomputable def firstLayerIncidenceSlot
    (Delta : VanKampen.DiscDiagram (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (depth scale loss perimeter : ℕ)
    (C : CenteredWindowFirstLayerIncidence Delta P depth scale loss perimeter)
    (i : Fin depth) (q : Fin (scale - loss)) : Fin perimeter :=
  Fin.castLE (by
    rw [(Delta.faceBoundary (C.face i q)).length_eq_degree]
    exact C.faceDegree_le i q)
    (firstLayerIncidenceIndex Delta P depth scale loss perimeter C i q)

/-! ## The injection and its numerical consequence -/

/-- The first-face assignment produces the exact layer injection. -/
noncomputable def layerIncidenceInjection_of_firstLayer
    (Delta : VanKampen.DiscDiagram (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (depth scale loss perimeter : ℕ)
    (C : CenteredWindowFirstLayerIncidence Delta P depth scale loss perimeter) :
    LayerIncidenceInjection
      (fun i : Fin depth ↦ innerBoundaryFaceStarLayer Delta P i)
      scale loss perimeter := by
  classical
  refine {
    encode := fun i q ↦
      (⟨C.face i q, C.face_mem i q⟩,
        firstLayerIncidenceSlot Delta P depth scale loss perimeter C i q)
    injective := ?_ }
  intro i x y hxy
  have hface : C.face i x = C.face i y :=
    congrArg (fun p ↦ (p.1.1 : Delta.toCombMap.Face)) hxy
  have hslot := congrArg Prod.snd hxy
  have hslot_val := congrArg Fin.val hslot
  clear hxy
  cases hface
  have hindex :
      firstLayerIncidenceIndex Delta P depth scale loss perimeter C i x =
        firstLayerIncidenceIndex Delta P depth scale loss perimeter C i y := by
    apply Fin.ext
    change
      (firstLayerIncidenceIndex Delta P depth scale loss perimeter C i x).val =
        (firstLayerIncidenceIndex Delta P depth scale loss perimeter C i y).val
    exact hslot_val
  have hgetx := firstLayerIncidenceIndex_get
    Delta P depth scale loss perimeter C i x
  have hgety := firstLayerIncidenceIndex_get
    Delta P depth scale loss perimeter C i y
  have hdart : P.darts.get (C.position i x) =
      P.darts.get (C.position i y) := by
    rw [← hgetx, ← hgety, hindex]
  exact C.position_injective i
    ((boundarySubpath_nodup Delta P).get_inj_iff.mp hdart)

/-- An incidence injection gives the per-layer covering inequality. -/
theorem layer_covers_of_incidenceInjection
    {Face : Type}
    {layer : Fin depth → Finset Face} {scale loss perimeter : ℕ}
    (C : LayerIncidenceInjection layer scale loss perimeter) :
    ∀ i : Fin depth, scale - loss ≤ perimeter * (layer i).card := by
  classical
  intro i
  have hcard := Fintype.card_le_of_injective (C.encode i) (C.injective i)
  have hsetcard : Fintype.card {face // face ∈ (layer i : Set Face)} =
      (layer i).card := by
    calc
      Fintype.card {face // face ∈ (layer i : Set Face)} =
          Nat.card {face // face ∈ (layer i : Set Face)} :=
        (Nat.card_eq_fintype_card).symm
      _ = (layer i : Set Face).ncard := rfl
      _ = (layer i).card := Set.ncard_coe_finset _
  simpa only [Fintype.card_fin, Fintype.card_prod, hsetcard,
    Nat.mul_comm] using hcard

/-- The numerical covering predicate used by the successive-star record. -/
abbrev LayerCoversWindow
    (Delta : VanKampen.DiscDiagram (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (depth scale loss perimeter : ℕ) : Prop :=
  ∀ i : Fin depth, scale - loss ≤ perimeter *
    (innerBoundaryFaceStarLayer Delta P (i : ℕ)).card

omit [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
/-- The centered first-face data supplies `LayerCoversWindow`. -/
theorem layerCoversWindow_of_firstLayer
    (Delta : VanKampen.DiscDiagram (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (depth scale loss perimeter : ℕ)
    (C : CenteredWindowFirstLayerIncidence Delta P depth scale loss perimeter) :
    LayerCoversWindow Delta P depth scale loss perimeter :=
  layer_covers_of_incidenceInjection
    (layerIncidenceInjection_of_firstLayer Delta P depth scale loss perimeter C)

/-! ## One-triangle model -/

/-- The six-dart one-triangle layer has a nonempty zero layer. -/
theorem oneTriangle_zeroLayer_nonempty :
    (VanKampen.oneTriangleCombMap.faceStarLayer
      (Finset.univ : Finset VanKampen.oneTriangleCombMap.Face) 0).Nonempty := by
  classical
  rw [VanKampen.CombMap.faceStarLayer, if_pos rfl]
  exact ⟨VanKampen.oneTriangleCombMap.faceOf (0, false), Finset.mem_univ _⟩

/-- The unit one-triangle layer admits an explicit incidence injection. -/
noncomputable def oneTriangle_unitIncidenceInjection :
    LayerIncidenceInjection
      (fun _ : Fin 1 ↦ VanKampen.oneTriangleCombMap.faceStarLayer
        (Finset.univ : Finset VanKampen.oneTriangleCombMap.Face) 0)
      1 0 1 := by
  classical
  refine {
    encode := fun _ _ ↦
      (⟨VanKampen.oneTriangleCombMap.faceOf (0, false), ?_⟩, 0)
    injective := ?_ }
  · rw [VanKampen.CombMap.faceStarLayer, if_pos rfl]
    exact Finset.mem_univ _
  · intro _i x y _hxy
    apply Fin.ext
    omega

/-- The incidence theorem recovers the unit covering inequality in the
one-triangle model. -/
theorem oneTriangle_unit_cover_of_incidenceInjection :
    ∀ _i : Fin 1, 1 - 0 ≤ 1 *
      (VanKampen.oneTriangleCombMap.faceStarLayer
        (Finset.univ : Finset VanKampen.oneTriangleCombMap.Face) 0).card :=
  layer_covers_of_incidenceInjection oneTriangle_unitIncidenceInjection

end Table
end GirthEightPrimitives2
end GGT
end GroupApproximation
