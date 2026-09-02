import GroupApproximation.GGT.VanKampen.FaceSetMoveAlgebra

/-!
# The value of an assembled closed walk

Every consumer of a face-set peeling uses it only through
`FaceSetBoundaryPeeling.to_homotopy` or `FaceSetBoundary.cycle_value_eq_one`;
nothing inspects the deletion schedule.  So the load-bearing content is a value
identity for the boundary walk, not a schedule.

`FaceAssembly Delta l walk` records that `walk` was built from the empty walk by
inserting complete face boundaries, whose faces are listed in `l`, and
cancelling `alpha`-pairs.  Walks are ordinary lists: darts may repeat and the
walk may pass through a pinch vertex, so nothing here needs a single boundary
cycle, an unpinched face, or an ear.

`closedWalk_value_eq_one_of_gCells` is then the van Kampen conclusion for a
`G`-cell region, with no planarity used at all.

## What planarity is still for

The general form "the value of a closed walk is the product of the conjugated
values of the faces it encloses" is not stated here, because *encloses* has no
meaning without planarity: on a surface which is not simply connected a closed
walk need not bound the faces inside it in any sense, and the identity is false.
`FaceAssembly` replaces enclosure by an explicit construction, which is exactly
the data a planar argument would have to produce.  So the planar input has not
been removed, it has been isolated: what remains is
`RegionFaceAssemblyStatement`, that the boundary cycle of a selected face set
admits an assembly from its own faces.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Embedded

open GroupApproximation.HullSC

universe u w v

/-- A closed walk built from the empty walk by inserting complete face
boundaries and cancelling `alpha`-pairs.  The first index lists the faces
inserted, so a value identity can be read off it. -/
inductive FaceAssembly {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) :
    List Delta.toCombMap.Face → List Delta.toCombMap.Dart → Prop
  | empty : FaceAssembly Delta [] []
  | insertFace {l : List Delta.toCombMap.Face}
      {before after : List Delta.toCombMap.Dart}
      (face : Delta.toCombMap.Face)
      (rest : FaceAssembly Delta l (before ++ after)) :
      FaceAssembly Delta (face :: l)
        (before ++ (Delta.faceBoundary face).darts ++ after)
  | insertPair {l : List Delta.toCombMap.Face}
      {before after : List Delta.toCombMap.Dart}
      (dart : Delta.toCombMap.Dart)
      (rest : FaceAssembly Delta l (before ++ after)) :
      FaceAssembly Delta l
        (before ++ dart :: Delta.toCombMap.alpha dart :: after)

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

/-! ## The value identity -/

/-- An assembled closed walk whose faces are all `G`-cells has value one.  This
is the van Kampen conclusion the peeling was only ever used for, and it uses no
planarity. -/
theorem closedWalk_value_eq_one_of_gCells
    {l : List Delta.toCombMap.Face} {walk : List Delta.toCombMap.Dart}
    (assembly : FaceAssembly Delta l walk)
    (hcells : ∀ f ∈ l, GGT.RelLetter.listVal (Delta.faceWord f) = 1) :
    GGT.RelLetter.listVal (dartWord Delta walk) = 1 := by
  revert hcells
  induction assembly with
  | empty =>
      intro _
      simp [dartWord, GGT.RelLetter.listVal]
  | insertFace face rest ih =>
      intro hcells
      have hface : GGT.RelLetter.listVal
          (dartWord Delta (Delta.faceBoundary face).darts) = 1 := by
        have hval := hcells face (List.mem_cons_self face _)
        simpa only [dartWord, DiscDiagram.faceWord] using hval
      have hrest := ih (fun f hf => hcells f (List.mem_cons_of_mem face hf))
      rw [dartWord_append, RelWord.listVal_append] at hrest
      rw [dartWord_append, dartWord_append, RelWord.listVal_append,
        RelWord.listVal_append, hface, mul_one]
      exact hrest
  | insertPair dart rest ih =>
      intro hcells
      rw [listVal_dartWord_erase_alpha_pair]
      exact ih hcells

/-! ## Compatibility with the existing face-pasting relation -/

/-- An assembly from faces of a selected set is a face-set word homotopy to the
empty word, so nothing downstream loses information by taking assemblies as the
primitive notion. -/
theorem faceSetWordHomotopy_of_faceAssembly
    {faces : Finset Delta.toCombMap.Face}
    {l : List Delta.toCombMap.Face} {walk : List Delta.toCombMap.Dart}
    (assembly : FaceAssembly Delta l walk)
    (hl : ∀ f ∈ l, f ∈ faces) :
    FaceSetWordHomotopy Delta faces walk [] := by
  revert hl
  induction assembly with
  | empty =>
      intro _
      exact FaceSetWordHomotopy.refl []
  | insertFace face rest ih =>
      intro hl
      have hface : face ∈ faces := hl face (List.mem_cons_self face _)
      have hstep : FaceSetWordHomotopy Delta faces
          (_ ++ (Delta.faceBoundary face).darts ++ _) (_ ++ _) :=
        FaceSetWordHomotopy.eraseFace face hface _ _
      exact hstep.trans (ih (fun f hf => hl f (List.mem_cons_of_mem face hf)))
  | insertPair dart rest ih =>
      intro hl
      have hstep : FaceSetWordHomotopy Delta faces
          (_ ++ dart :: Delta.toCombMap.alpha dart :: _) (_ ++ _) :=
        FaceSetWordHomotopy.eraseAlphaPair dart _ _
      exact hstep.trans (ih hl)

/-- An assembly of a boundary cycle from the selected faces gives the boundary
value identity used by every consumer. -/
theorem cycle_value_eq_one_of_faceAssembly
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces)
    {l : List Delta.toCombMap.Face}
    (hl : ∀ f ∈ l, f ∈ faces)
    (assembly : FaceAssembly Delta l boundary.cycle) :
    GGT.RelLetter.listVal (dartWord Delta boundary.cycle) = 1 :=
  closedWalk_value_eq_one_of_gCells assembly
    (fun f hf => (boundary.all_gCells f (hl f hf)).2)

/-- An assembly of a boundary cycle also gives the face-pasting homotopy, which
is the exact shape the Hull49 and estimating consumers take. -/
theorem faceSetWordHomotopy_of_boundary_faceAssembly
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces)
    {l : List Delta.toCombMap.Face}
    (hl : ∀ f ∈ l, f ∈ faces)
    (assembly : FaceAssembly Delta l boundary.cycle) :
    FaceSetWordHomotopy Delta faces boundary.cycle [] :=
  faceSetWordHomotopy_of_faceAssembly assembly hl

end Embedded

/-! ## The remaining statement -/

/-- The one fact still missing: the boundary cycle of a selected face set can be
assembled from that set's own faces.  This is where planarity enters, and it is
the only place it is needed for the value identity. -/
def RegionFaceAssemblyStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (boundary : Embedded.FaceSetBoundary Delta faces),
    ∃ l : List Delta.toCombMap.Face, (∀ f ∈ l, f ∈ faces) ∧
      Embedded.FaceAssembly Delta l boundary.cycle

/-- The assembly statement gives the face-pasting homotopy for every selected
face set, with no ear, no unpinched face and no single-cycle remainder. -/
theorem faceSetWordHomotopy_of_regionAssembly
    (hassembly : RegionFaceAssemblyStatement.{u, w, v})
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (boundary : Embedded.FaceSetBoundary Delta faces) :
    Embedded.FaceSetWordHomotopy Delta faces boundary.cycle [] := by
  obtain ⟨l, hl, assembly⟩ := hassembly boundary
  exact Embedded.faceSetWordHomotopy_of_boundary_faceAssembly boundary hl assembly

end VanKampen
end GGT
end GroupApproximation
