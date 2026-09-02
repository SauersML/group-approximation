import GroupApproximation.GGT.KazhdanHypGirthEightDiagram
import GroupApproximation.GGT.VanKampen.CactusRealization
import GroupApproximation.GGT.VanKampen.Surgery

/-!
# Relator-cell coverage and identity reduction

This module isolates the presentation-independent part of base-cell
elimination.  Under explicit coverage of every inner face by a stored relator
cell, the original diagram is already relator-only, so its boundary word,
relator area, and reducedness are preserved by equality.

The face-count theorem also proves that free-group cells contribute zero to the
curvature count under the same hypothesis: `rCellCount = innerFaceCount`.
This is the base-cell step required before the triangular Euler estimate in
`KazhdanHypGirthEightFromDiagram`.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

universe u w v

/-! ## Generic coverage by stored relator cells -/

/-- Every non-outer face of a disc diagram is represented by a stored relator
cell.  For triangular presentations this is the first field of
`TriangularDiagramLocalData`. -/
structure RelatorCellCover
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) : Prop where
  /-- A non-outer face has a stored relator cell with exactly that face. -/
  cell : ∀ f, f ≠ Delta.outerFace →
    ∃ C ∈ Delta.relatorCells, C.face = f

namespace RelatorCellCover

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

/-- Coverage by stored cells identifies membership in the relator-face list
with membership among all inner faces. -/
theorem relatorFace_mem_iff_innerFace (R : RelatorCellCover Delta)
    (f : Delta.toCombMap.Face) :
    f ∈ Delta.relatorCells.map RelatorCell.face ↔ f ∈ Delta.innerFaces := by
  constructor
  · intro hf
    obtain ⟨C, hCmem, hCface⟩ := List.mem_map.mp hf
    subst f
    simpa only [DiscDiagram.innerFaces, Finset.mem_sdiff, Finset.mem_univ,
      true_and, Finset.mem_singleton] using C.face_ne_outer
  · intro hf
    have hfne : f ≠ Delta.outerFace := by
      simpa only [DiscDiagram.innerFaces, Finset.mem_sdiff, Finset.mem_univ,
        true_and, Finset.mem_singleton] using hf
    obtain ⟨C, hCmem, hCface⟩ := R.cell f hfne
    apply List.mem_map.mpr
    exact ⟨C, hCmem, hCface⟩

/-- If every inner face is a stored relator cell, relator area equals the full
inner-face count.  Thus no free-group face enters the curvature estimate. -/
theorem rCellCount_eq_innerFaceCount (R : RelatorCellCover Delta) :
    Delta.rCellCount = Delta.innerFaceCount := by
  classical
  have hfaces : (Delta.relatorCells.map RelatorCell.face).toFinset =
      Delta.innerFaces := by
    ext f
    rw [List.mem_toFinset]
    exact R.relatorFace_mem_iff_innerFace f
  calc
    Delta.rCellCount =
        (Delta.relatorCells.map RelatorCell.face).length := by
      simp only [DiscDiagram.rCellCount, List.length_map]
    _ = (Delta.relatorCells.map RelatorCell.face).toFinset.card :=
      (List.toFinset_card_of_nodup Delta.relatorCell_faces_nodup).symm
    _ = Delta.innerFaces.card := congrArg Finset.card hfaces
    _ = Delta.innerFaceCount := rfl

/-- The count equality sharpens the generic inequality
`rCellCount ≤ innerFaceCount`. -/
theorem innerFaceCount_le_rCellCount (R : RelatorCellCover Delta) :
    Delta.innerFaceCount ≤ Delta.rCellCount := by
  rw [R.rCellCount_eq_innerFaceCount]

end RelatorCellCover

/-! ## Exact-boundary retyping of the cactus complement -/

/-- A cactus complement can be retyped away from the distinguished base cell
when an explicit relator-only retyping is supplied.  The fields record only
the boundary, area, and reducedness consequences used by a literal filling. -/
structure CactusRelatorRetyping
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) where
  diagram : DiscDiagram.{u, w, v} W
  boundaryWord_eq : diagram.boundaryWord = Delta.boundaryWord
  relatorOnly : RelatorCellCover diagram
  rCellCount_le : diagram.rCellCount ≤ Delta.rCellCount
  reduced : diagram.Reduced
  planar : diagram.toCombMap.IsPlanar

/-! ## Concrete surgery certificates -/

/-- A concrete free-base-cell deletion certificate.  The selected region is
reclosed by `Surgery.MapCollapse.replaceGRegion`; its face words are trivial
in the free base group, and the replacement diagram has only the retained
relator cells. -/
structure CactusBaseCellDeletion
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) where
  bigFace : Delta.toCombMap.Face
  faces : Finset Delta.toCombMap.Face
  bigFace_mem : bigFace ∈ faces
  baseWord_one : ∀ f, f ∈ faces →
    GGT.RelLetter.listVal (Delta.faceWord f) = 1
  region : Surgery.MapCollapse.IsDiscRegion Delta.toCombMap faces
  replacement : Surgery.GRegionReplacement.{u, w, v, v} Delta
  replacement_map_eq : replacement.diagram.toCombMap =
    Surgery.MapCollapse.replaceGRegion Delta.toCombMap faces region
  relatorOnly : RelatorCellCover replacement.diagram
  reduced : Delta.Reduced

/-- The explicit combinatorial map obtained by deleting the selected cactus
region and re-closing its trimmed boundary cycle. -/
noncomputable def CactusBaseCellDeletion.surgeryMap
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (C : CactusBaseCellDeletion Delta) : CombMap.{v} :=
  Surgery.MapCollapse.replaceGRegion Delta.toCombMap C.faces C.region

/-- The explicit map is the map stored by the landed diagram replacement. -/
theorem CactusBaseCellDeletion.surgeryMap_eq_replacement
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (C : CactusBaseCellDeletion Delta) :
    C.surgeryMap = C.replacement.diagram.toCombMap := by
  exact C.replacement_map_eq.symm

/-- Planarity of the source disc is preserved by the concrete cactus map
deletion. -/
theorem CactusBaseCellDeletion.surgeryMap_planar
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (C : CactusBaseCellDeletion Delta)
    (hplanar : Delta.toCombMap.IsPlanar) :
    C.surgeryMap.IsPlanar := by
  unfold CactusBaseCellDeletion.surgeryMap
  exact Surgery.MapCollapse.replaceGRegion_planar
    Delta.toCombMap C.faces C.region hplanar

/-- The concrete cactus map deletion has the replacement's literal boundary
word. -/
theorem CactusBaseCellDeletion.surgeryMap_boundaryWord_eq
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (C : CactusBaseCellDeletion Delta) :
    C.replacement.diagram.boundaryWord = Delta.boundaryWord :=
  C.replacement.outerWord_eq

/-- A finite sequence of landed cactus folds.  Each step is a concrete
`replaceGRegion` surgery and records the one-face inner-area drop. -/
inductive CactusFoldChain
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))} :
    DiscDiagram.{u, w, v} W → DiscDiagram.{u, w, v} W → ℕ →
      Type (max (max (u + 1) (v + 2)) (w + 1))
  | done {Delta : DiscDiagram.{u, w, v} W}
      (cover : RelatorCellCover Delta) :
      CactusFoldChain Delta Delta 0
  | step {Delta Next : DiscDiagram.{u, w, v} W} {k : ℕ}
      (C : CactusBaseCellDeletion Delta)
      (tail : CactusFoldChain C.replacement.diagram Next k)
      (area_drop : C.replacement.diagram.innerFaceCount + 1 =
        Delta.innerFaceCount) :
      CactusFoldChain Delta Next (k + 1)

/-- The recorded one-face drops add exactly along a cactus fold chain. -/
theorem CactusFoldChain.innerFaceCount_eq_add_length
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta Next : DiscDiagram.{u, w, v} W} {k : ℕ}
    (chain : CactusFoldChain Delta Next k) :
    Next.innerFaceCount + k = Delta.innerFaceCount := by
  induction chain with
  | done cover => simp
  | @step Delta Next k C tail area_drop ih =>
      omega

/-- Induction over the landed cactus folds composes their boundary, reducedness,
planarity, and relator-only fields into one `CactusRelatorRetyping`. -/
noncomputable def CactusFoldChain.toRetyping
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta Next : DiscDiagram.{u, w, v} W} {k : ℕ}
    (chain : CactusFoldChain Delta Next k)
    (hplanar : Delta.toCombMap.IsPlanar)
    (hred : Delta.Reduced) : CactusRelatorRetyping Delta := by
  induction chain generalizing hplanar hred with
  | done cover =>
      exact {
        diagram := Delta
        boundaryWord_eq := rfl
        relatorOnly := cover
        rCellCount_le := le_rfl
        reduced := hred
        planar := hplanar }
  | @step Delta Next k C tail area_drop ih =>
      have hnextPlanar : C.replacement.diagram.toCombMap.IsPlanar := by
        rw [← C.surgeryMap_eq_replacement]
        exact C.surgeryMap_planar hplanar
      have hnextRed : C.replacement.diagram.Reduced :=
        C.replacement.reduced C.reduced
      let R := ih hnextPlanar hnextRed
      refine {
        diagram := R.diagram
        boundaryWord_eq := R.boundaryWord_eq.trans
          C.surgeryMap_boundaryWord_eq
        relatorOnly := R.relatorOnly
        rCellCount_le := ?_
        reduced := R.reduced
        planar := R.planar }
      exact R.rCellCount_le.trans_eq C.replacement.rCellCount_eq

/-- The concrete reclosed replacement supplies every field of
`CactusRelatorRetyping`.  The boundary is unchanged by the surgery, relator
area is unchanged by the ordered cell equivalence, and reducedness transports
along that equivalence. -/
def CactusBaseCellDeletion.toRetyping
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (C : CactusBaseCellDeletion Delta)
    (hplanar : Delta.toCombMap.IsPlanar) : CactusRelatorRetyping Delta where
  diagram := C.replacement.diagram
  boundaryWord_eq := C.replacement.outerWord_eq
  relatorOnly := C.relatorOnly
  rCellCount_le := by
    rw [C.replacement.rCellCount_eq]
  reduced := C.replacement.reduced C.reduced
  planar := by
    rw [← C.surgeryMap_eq_replacement]
    exact C.surgeryMap_planar hplanar

/-- The generic cactus constructor under the source disc's planarity field.
The deletion witness supplies the endpoint trimming and free-base-cell fold. -/
def cactusRelatorRetyping_of_planarDisc
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (hplanar : Delta.toCombMap.IsPlanar)
    (C : CactusBaseCellDeletion Delta) : CactusRelatorRetyping Delta :=
  C.toRetyping hplanar

/-- The planar cactus constructor preserves a repeated boundary power. -/
theorem cactusRelatorRetyping_of_planarDiscPower
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (hplanar : Delta.toCombMap.IsPlanar)
    (C : CactusBaseCellDeletion Delta)
    (word : List (GGT.RelLetter G Lambda)) (n : ℕ)
    (hpower : Delta.boundaryWord = (List.replicate n word).flatten) :
    ∃ R : CactusRelatorRetyping Delta,
      R.diagram.boundaryWord = (List.replicate n word).flatten := by
  let R := cactusRelatorRetyping_of_planarDisc hplanar C
  refine ⟨R, ?_⟩
  exact R.boundaryWord_eq.trans hpower

/-- The retyped cactus is an exact-boundary relator-only disc. -/
theorem exactBoundaryRelatorOnly_of_cactusRetyping
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (C : CactusRelatorRetyping Delta) :
    ∃ D : DiscDiagram.{u, w, v} W,
      D.boundaryWord = Delta.boundaryWord ∧
      RelatorCellCover D ∧ D.Reduced ∧ D.rCellCount ≤ Delta.rCellCount :=
  ⟨C.diagram, C.boundaryWord_eq, C.relatorOnly, C.reduced, C.rCellCount_le⟩

/-! ## Cancellation surgery output -/

/-- Output of cutting a mirror relator-cell pair and re-closing the
complementary boundary.  The area equation is the sole numerical fact needed
to turn the topological cut into a strict least-area contradiction. -/
structure MirrorPairCut
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) where
  result : DiscDiagram.{u, w, v} W
  boundaryWord_eq : result.boundaryWord = Delta.boundaryWord
  relatorOnly : RelatorCellCover result
  reduced : result.Reduced
  area_eq : result.rCellCount + 2 = Delta.rCellCount
  planar : result.toCombMap.IsPlanar

/-- Data for the actual two-cell cut.  The `GRegionReplacement` is the
reclosed map after the two mirror faces are deleted.  The list equation says
that exactly those two ordered relator cells disappear; the area drop is then
proved by list-length arithmetic. -/
structure MirrorPairDeletion
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) where
  pre : List (RelatorCell Delta.toCombMap Delta.outerFace W)
  between : List (RelatorCell Delta.toCombMap Delta.outerFace W)
  suf : List (RelatorCell Delta.toCombMap Delta.outerFace W)
  first : RelatorCell Delta.toCombMap Delta.outerFace W
  second : RelatorCell Delta.toCombMap Delta.outerFace W
  old_cells : Delta.relatorCells =
    pre ++ first :: (between ++ second :: suf)
  replacement : Surgery.GRegionReplacement.{u, w, v, v} Delta
  new_cells : replacement.diagram.relatorCells =
    pre.map replacement.cells.cellEquiv ++
      between.map replacement.cells.cellEquiv ++
      suf.map replacement.cells.cellEquiv
  relatorOnly : RelatorCellCover replacement.diagram
  mirror : (between.map RelatorCell.value).prod⁻¹ * first.value *
      (between.map RelatorCell.value).prod * second.value = 1
  faces : Finset Delta.toCombMap.Face
  region : Surgery.MapCollapse.IsDiscRegion Delta.toCombMap faces
  replacement_map_eq : replacement.diagram.toCombMap =
    Surgery.MapCollapse.replaceGRegion Delta.toCombMap faces region

/-- The explicit combinatorial map obtained by deleting the two mirror faces
and re-closing their two trimmed complementary boundary paths. -/
noncomputable def MirrorPairDeletion.surgeryMap
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (C : MirrorPairDeletion Delta) : CombMap.{v} :=
  Surgery.MapCollapse.replaceGRegion Delta.toCombMap C.faces C.region

/-- The explicit mirror-surgery map is the map stored by the landed diagram
replacement. -/
theorem MirrorPairDeletion.surgeryMap_eq_replacement
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (C : MirrorPairDeletion Delta) :
    C.surgeryMap = C.replacement.diagram.toCombMap := by
  exact C.replacement_map_eq.symm

/-- Planarity of the source disc is preserved by the concrete mirror cut. -/
theorem MirrorPairDeletion.surgeryMap_planar
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (C : MirrorPairDeletion Delta)
    (hplanar : Delta.toCombMap.IsPlanar) :
    C.surgeryMap.IsPlanar := by
  unfold MirrorPairDeletion.surgeryMap
  exact Surgery.MapCollapse.replaceGRegion_planar
    Delta.toCombMap C.faces C.region hplanar

/-- The concrete mirror-surgery map has the same literal exterior word. -/
theorem MirrorPairDeletion.surgeryMap_boundaryWord_eq
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (C : MirrorPairDeletion Delta) :
    C.replacement.diagram.boundaryWord = Delta.boundaryWord :=
  C.replacement.outerWord_eq

/-- The two-cell cut lowers ordered relator area by exactly two. -/
theorem MirrorPairDeletion.area_drop
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (C : MirrorPairDeletion Delta) :
    C.replacement.diagram.rCellCount + 2 = Delta.rCellCount := by
  change C.replacement.diagram.relatorCells.length + 2 =
    Delta.relatorCells.length
  have hOld := congrArg List.length C.old_cells
  have hNew := congrArg List.length C.new_cells
  simp only [List.length_append, List.length_cons, List.length_map] at hOld hNew
  have hcount := C.replacement.rCellCount_eq
  change C.replacement.diagram.relatorCells.length =
    Delta.relatorCells.length at hcount
  omega

/-- In the two-cell model, the concrete cut has zero relator cells left. -/
theorem MirrorPairDeletion.area_zero_of_twoCell
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (C : MirrorPairDeletion Delta)
    (htwo : Delta.relatorCells.length = 2) :
    C.replacement.diagram.rCellCount = 0 := by
  have hdrop := C.area_drop
  change C.replacement.diagram.relatorCells.length + 2 =
    Delta.relatorCells.length at hdrop
  rw [htwo] at hdrop
  change C.replacement.diagram.relatorCells.length = 0
  omega

/-- The concrete two-cell cut supplies the abstract mirror-pair certificate.
Reducedness is transported from the old diagram and the boundary word is
preserved by the reclosure. -/
def MirrorPairDeletion.toMirrorPairCut
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (C : MirrorPairDeletion Delta) (hred : Delta.Reduced)
    (hplanar : Delta.toCombMap.IsPlanar) :
    MirrorPairCut Delta where
  result := C.replacement.diagram
  boundaryWord_eq := C.replacement.outerWord_eq
  relatorOnly := C.relatorOnly
  reduced := C.replacement.reduced hred
  area_eq := C.area_drop
  planar := by
    rw [← C.surgeryMap_eq_replacement]
    exact C.surgeryMap_planar hplanar

/-- The generic mirror constructor exposes the planar output of the
reclosure and the exact two-cell area drop. -/
def mirrorPairCut_of_planarDisc
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (C : MirrorPairDeletion Delta) (hred : Delta.Reduced)
    (hplanar : Delta.toCombMap.IsPlanar) :
    MirrorPairCut Delta :=
  C.toMirrorPairCut hred hplanar

/-- A mirror-pair cut strictly lowers relator area. -/
theorem MirrorPairCut.area_lt
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} (C : MirrorPairCut Delta) :
    C.result.rCellCount < Delta.rCellCount := by
  have harea := C.area_eq
  omega

/-- The exact-boundary output of a mirror-pair cut supplies the strict
area-decrease premise used by least-power reduction. -/
theorem exists_strict_cut_of_mirrorPairCut
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} (C : MirrorPairCut Delta) :
    ∃ D : DiscDiagram.{u, w, v} W,
      D.boundaryWord = Delta.boundaryWord ∧ D.rCellCount < Delta.rCellCount :=
  ⟨C.result, C.boundaryWord_eq, C.area_lt⟩

/-! ## Degenerate model checks -/

/-- A zero-cell diagram cannot contain a mirror pair, so the cancellation
premise is empty in the one-face model. -/
theorem no_mirror_pair_of_empty_relatorCells
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (hzero : Delta.relatorCells = []) :
    ¬ ∃ C : RelatorCell Delta.toCombMap Delta.outerFace W,
      C ∈ Delta.relatorCells := by
  intro h
  obtain ⟨C, hC⟩ := h
  rw [hzero] at hC
  simp at hC

/-! ## Presentation-independent identity reduction -/

/-- A covered diagram needs no topological change: it is the required
relator-only output with literal boundary and area preserved by equality. -/
structure IdentityRelatorOnlyReduction
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) where
  /-- The output diagram. -/
  diagram : DiscDiagram.{u, w, v} W
  /-- Its boundary word is literally unchanged. -/
  boundaryWord_eq : diagram.boundaryWord = Delta.boundaryWord
  /-- Its ordered relator area is literally unchanged. -/
  rCellCount_eq : diagram.rCellCount = Delta.rCellCount
  /-- Diagram reducedness is preserved. -/
  reduced : diagram.Reduced
  /-- Every output inner face is a stored relator cell. -/
  cover : RelatorCellCover diagram

/-- Explicit relator-cell coverage constructs the identity reduction. -/
def identityRelatorOnlyReduction
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (R : RelatorCellCover Delta)
    (hred : Delta.Reduced) : IdentityRelatorOnlyReduction Delta where
  diagram := Delta
  boundaryWord_eq := rfl
  rCellCount_eq := rfl
  reduced := hred
  cover := R

/-- The identity reduction preserves the sharp relator/inner-face count. -/
theorem identityRelatorOnlyReduction_count
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} (R : RelatorCellCover Delta)
    (hred : Delta.Reduced) :
    (identityRelatorOnlyReduction Delta R hred).diagram.rCellCount =
      (identityRelatorOnlyReduction Delta R hred).diagram.innerFaceCount :=
  R.rCellCount_eq_innerFaceCount

end VanKampen
end GGT
end GroupApproximation
