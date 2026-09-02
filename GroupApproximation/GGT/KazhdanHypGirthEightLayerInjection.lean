import GroupApproximation.GGT.KazhdanHypGirthEightVKInterface
import GroupApproximation.GGT.VanKampen.DiscDiagram
import GroupApproximation.GGT.VanKampen.CombMapStars

/-!
# Incidences in successive face-star layers

This is the clean layer-injection module for the girth-eight construction.
It deliberately does not import `KazhdanHypGirthEightPrimitives2`: the
interface below is the part needed by that module, while its larger import
closure is currently under repair.

For a centered boundary window, `CenteredWindowLayerCover` records the
surviving positions and the fact that the successive-star layers cover them.
The first face is selected from that cover, so
`CenteredWindowFirstLayerIncidence` is constructed rather than assumed.
`firstLayerIncidenceIndex` reads the position back from the duplicate-free
face boundary, and `firstLayerIncidenceSlot` places that index in the uniform
perimeter range.  The resulting `LayerIncidenceInjection` gives the exact
numerical consequence consumed by the successive-star estimate.

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
  have hdisjoint :
      Disjoint (Delta.toCombMap.faceStarLayer (boundaryFaceSeed Delta P) i)
        (Delta.toCombMap.faceStarLayer (boundaryFaceSeed Delta P) j) := by
    have hballMono : ∀ {a b : ℕ}, a ≤ b →
        Delta.toCombMap.faceStarBall (boundaryFaceSeed Delta P) a ⊆
          Delta.toCombMap.faceStarBall (boundaryFaceSeed Delta P) b := by
      intro a b hab
      induction b, hab using Nat.le_induction with
      | base => exact fun _ h => h
      | succ b _ ih =>
          exact ih.trans (by
            change Delta.toCombMap.faceStarBall
              (boundaryFaceSeed Delta P) b ⊆
              Delta.toCombMap.faceStarSet
                (Delta.toCombMap.faceStarBall (boundaryFaceSeed Delta P) b)
            exact VanKampen.CombMap.subset_faceStarSet Delta.toCombMap _)
    wlog hlt : i < j generalizing i j with H
    · exact (H hij.symm (by omega)).symm
    have hjpos : j ≠ 0 := by omega
    rw [Finset.disjoint_left]
    intro face hfi hfj
    have hfiBall : face ∈
        Delta.toCombMap.faceStarBall (boundaryFaceSeed Delta P) i :=
      by
        by_cases hi : i = 0
        · subst i
          simpa [VanKampen.CombMap.faceStarLayer,
            VanKampen.CombMap.faceStarBall] using hfi
        · have hfi' : face ∈
              Delta.toCombMap.faceStarBall (boundaryFaceSeed Delta P) i ∧
              face ∉ Delta.toCombMap.faceStarBall
                (boundaryFaceSeed Delta P) (i - 1) := by
            simpa [VanKampen.CombMap.faceStarLayer, hi] using hfi
          exact hfi'.1
    have hijpred : i ≤ j - 1 := by omega
    have hfpred : face ∈
        Delta.toCombMap.faceStarBall (boundaryFaceSeed Delta P) (j - 1) :=
      hballMono hijpred hfiBall
    have hfj' : face ∈
        (Delta.toCombMap.faceStarBall (boundaryFaceSeed Delta P) j \
          Delta.toCombMap.faceStarBall (boundaryFaceSeed Delta P) (j - 1)) := by
      simpa [VanKampen.CombMap.faceStarLayer, hjpos] using hfj
    exact (Finset.mem_sdiff.mp hfj').2 hfpred
  apply hdisjoint.mono
  · intro face hface
    exact (Finset.mem_inter.mp hface).1
  · intro face hface
    exact (Finset.mem_inter.mp hface).1

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

/-! ## The centered first-face certificate -/

/-- The set-cover statement needed to select the first face at every
surviving centered-window position.  The `firstFace` field is the covering
fact for successive star layers: it puts the boundary dart on an inner face
in the designated layer. -/
structure CenteredWindowLayerCover
    (Delta : VanKampen.DiscDiagram (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (depth scale loss perimeter : ℕ) where
  /-- The surviving boundary occurrence at each layer and position. -/
  position : ∀ _i : Fin depth, Fin (scale - loss) → Fin P.darts.length
  /-- Distinct positions give distinct boundary occurrences. -/
  position_injective : ∀ i : Fin depth, Function.Injective (position i)
  /-- The designated layer covers the boundary dart at the position. -/
  firstFace : ∀ (i : Fin depth) (q : Fin (scale - loss)),
    ∃ f : Delta.toCombMap.Face,
      f ∈ innerBoundaryFaceStarLayer Delta P (i : ℕ) ∧
      P.darts.get (position i q) ∈ (Delta.faceBoundary f).darts
  /-- Every face offered by the cover has the prescribed perimeter bound. -/
  faceDegree_le : ∀ (i : Fin depth) (_q : Fin (scale - loss))
    (f : Delta.toCombMap.Face),
    f ∈ innerBoundaryFaceStarLayer Delta P (i : ℕ) →
      Delta.toCombMap.faceDegree f ≤ perimeter

omit [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
/-- A centered layer cover supplies the first-face incidence data by choice. -/
noncomputable def centeredWindowFirstLayerIncidence_of_layerCover
    (Delta : VanKampen.DiscDiagram (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (depth scale loss perimeter : ℕ)
    (K : CenteredWindowLayerCover Delta P depth scale loss perimeter) :
    CenteredWindowFirstLayerIncidence Delta P depth scale loss perimeter := by
  classical
  exact {
    position := K.position
    position_injective := K.position_injective
    face := fun i q => Classical.choose (K.firstFace i q)
    face_mem := fun i q => (Classical.choose_spec (K.firstFace i q)).1
    on_face := fun i q => (Classical.choose_spec (K.firstFace i q)).2
    faceDegree_le := fun i q => K.faceDegree_le i q
      (Classical.choose (K.firstFace i q))
      (Classical.choose_spec (K.firstFace i q)).1 }

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

omit [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
/-- Transport a face-boundary lookup across an equality of faces when the
underlying incidence indices have the same natural-number value. -/
theorem faceBoundary_get_of_eq
    (Delta : VanKampen.DiscDiagram (triangleRelatorWords T))
    {f g : Delta.toCombMap.Face} (hfg : f = g)
    (ix : Fin (Delta.faceBoundary f).darts.length)
    (iy : Fin (Delta.faceBoundary g).darts.length)
    (hval : ix.val = iy.val) :
    (Delta.faceBoundary f).darts.get ix =
      (Delta.faceBoundary g).darts.get iy := by
  cases hfg
  have hxy : ix = iy := Fin.ext hval
  subst iy
  rfl

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
  have hslot := congrArg (fun p ↦ p.2) hxy
  dsimp at hslot
  unfold firstLayerIncidenceSlot at hslot
  have hslot_val :
      (firstLayerIncidenceIndex Delta P depth scale loss perimeter C i x).val =
        (firstLayerIncidenceIndex Delta P depth scale loss perimeter C i y).val := by
    simpa [firstLayerIncidenceSlot] using congrArg Fin.val hslot
  clear hslot
  clear hxy
  have hgetx := firstLayerIncidenceIndex_get
    Delta P depth scale loss perimeter C i x
  have hgety := firstLayerIncidenceIndex_get
    Delta P depth scale loss perimeter C i y
  have hboundary := faceBoundary_get_of_eq Delta hface
    (firstLayerIncidenceIndex Delta P depth scale loss perimeter C i x)
    (firstLayerIncidenceIndex Delta P depth scale loss perimeter C i y)
    hslot_val
  have hdart : P.darts.get (C.position i x) =
      P.darts.get (C.position i y) := by
    exact hgetx.symm.trans (hboundary.trans hgety)
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

omit [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
/-- The centered layer cover produces the incidence injection. -/
noncomputable def layerIncidenceInjection_of_layerCover
    (Delta : VanKampen.DiscDiagram (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (depth scale loss perimeter : ℕ)
    (K : CenteredWindowLayerCover Delta P depth scale loss perimeter) :
    LayerIncidenceInjection
      (fun i : Fin depth ↦ innerBoundaryFaceStarLayer Delta P (i : ℕ))
      scale loss perimeter :=
  layerIncidenceInjection_of_firstLayer Delta P depth scale loss perimeter
    (centeredWindowFirstLayerIncidence_of_layerCover
      Delta P depth scale loss perimeter K)

omit [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
/-- The centered layer cover produces the numerical covering inequality. -/
theorem layerCoversWindow_of_layerCover
    (Delta : VanKampen.DiscDiagram (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (depth scale loss perimeter : ℕ)
    (K : CenteredWindowLayerCover Delta P depth scale loss perimeter) :
    LayerCoversWindow Delta P depth scale loss perimeter :=
  layerCoversWindow_of_firstLayer Delta P depth scale loss perimeter
    (centeredWindowFirstLayerIncidence_of_layerCover
      Delta P depth scale loss perimeter K)

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

/-- The one-triangle zero layer covers the single unit-window position. -/
theorem oneTriangle_unit_firstFace_cover_model :
    ∀ _i : Fin 1, ∀ _q : Fin 1,
      ∃ f : VanKampen.oneTriangleCombMap.Face,
        f ∈ VanKampen.oneTriangleCombMap.faceStarLayer
          (Finset.univ : Finset VanKampen.oneTriangleCombMap.Face) 0 := by
  intro _i _q
  refine ⟨VanKampen.oneTriangleCombMap.faceOf (0, false), ?_⟩
  rw [VanKampen.CombMap.faceStarLayer, if_pos rfl]
  exact Finset.mem_univ _

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
