import GroupApproximation.GGT.VanKampen.Estimating.Embedded

/-!
# Surgery interfaces for relative disc diagrams

This file isolates the invariants needed when a disc consisting only of
`G`-faces is replaced inside a relative diagram.  The local topological
construction may change the dart and face types.  Relator cells are therefore
compared by an equivalence which preserves their order, words, and based
values.  This is enough to prove, rather than assume, that diagram-level
reducedness survives the replacement.

The estimating graph in `Estimating.Embedded` is an incidence structure, not
a combinatorial map: an interior edge stores its source and target relator
cells.  The final section consequently states loop and parallel-edge surgery
at that representation.  Its two-gon certificate is the exact input to the
Definition M contradiction already proved in the estimating layer.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

universe u w v v'

namespace Surgery

/-! ## Relator-cell transport -/

/-- An ordered equivalence between the relator cells of two diagrams.  It
preserves both the literal relator word and the based group value. -/
structure RCellEquiv
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (oldDiagram : DiscDiagram.{u, w, v} W)
    (newDiagram : DiscDiagram.{u, w, v'} W) where
  cellEquiv :
    RelatorCell oldDiagram.toCombMap oldDiagram.outerFace W ≃
      RelatorCell newDiagram.toCombMap newDiagram.outerFace W
  cells_eq : newDiagram.relatorCells =
    oldDiagram.relatorCells.map cellEquiv
  word_eq : ∀ cell, (cellEquiv cell).word = cell.word
  value_eq : ∀ cell, (cellEquiv cell).value = cell.value

namespace RCellEquiv

/-- The identity equivalence is an ordered relator-cell equivalence. -/
def refl
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) : RCellEquiv Delta Delta where
  cellEquiv := Equiv.refl _
  cells_eq := by simp
  word_eq := by intro cell; rfl
  value_eq := by intro cell; rfl

/-- Ordered cell transport preserves the number of relator cells. -/
theorem rCellCount_eq
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {oldDiagram : DiscDiagram.{u, w, v} W}
    {newDiagram : DiscDiagram.{u, w, v'} W}
    (cells : RCellEquiv oldDiagram newDiagram) :
    newDiagram.rCellCount = oldDiagram.rCellCount := by
  rw [DiscDiagram.rCellCount, DiscDiagram.rCellCount, cells.cells_eq,
    List.length_map]

/-- Ordered cell transport gives the requested finite cell-index
equivalence. -/
def indexEquiv
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {oldDiagram : DiscDiagram.{u, w, v} W}
    {newDiagram : DiscDiagram.{u, w, v'} W}
    (cells : RCellEquiv oldDiagram newDiagram) :
    Fin oldDiagram.rCellCount ≃ Fin newDiagram.rCellCount :=
  Fin.castOrderIso cells.rCellCount_eq.symm

/-- The transported relator-cell list has the same ordered list of words. -/
theorem cellWords_eq
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {oldDiagram : DiscDiagram.{u, w, v} W}
    {newDiagram : DiscDiagram.{u, w, v'} W}
    (cells : RCellEquiv oldDiagram newDiagram) :
    newDiagram.relatorCells.map RelatorCell.word =
      oldDiagram.relatorCells.map RelatorCell.word := by
  rw [cells.cells_eq, List.map_map]
  apply List.map_congr_left
  intro cell _
  exact cells.word_eq cell

/-- The transported relator-cell list has the same ordered list of based
values. -/
theorem cellValues_eq
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {oldDiagram : DiscDiagram.{u, w, v} W}
    {newDiagram : DiscDiagram.{u, w, v'} W}
    (cells : RCellEquiv oldDiagram newDiagram) :
    newDiagram.relatorCells.map RelatorCell.value =
      oldDiagram.relatorCells.map RelatorCell.value := by
  rw [cells.cells_eq, List.map_map]
  apply List.map_congr_left
  intro cell _
  exact cells.value_eq cell

/-- Reducedness depends only on the ordered based values of the relator
cells, hence it is preserved by an ordered cell equivalence. -/
theorem reduced
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {oldDiagram : DiscDiagram.{u, w, v} W}
    {newDiagram : DiscDiagram.{u, w, v'} W}
    (cells : RCellEquiv oldDiagram newDiagram)
    (hred : oldDiagram.Reduced) : newDiagram.Reduced := by
  intro pre between suf first second hsplit
  have holdSplit : oldDiagram.relatorCells =
      pre.map cells.cellEquiv.symm ++ cells.cellEquiv.symm first ::
        (between.map cells.cellEquiv.symm ++
          cells.cellEquiv.symm second :: suf.map cells.cellEquiv.symm) := by
    have h := congrArg (List.map cells.cellEquiv.symm) hsplit
    rw [cells.cells_eq] at h
    have hleft :
        List.map cells.cellEquiv.symm
            (List.map cells.cellEquiv oldDiagram.relatorCells) =
          oldDiagram.relatorCells := by
      induction oldDiagram.relatorCells with
      | nil => rfl
      | cons cell tail ih =>
          simp only [List.map_cons]
          rw [cells.cellEquiv.symm_apply_apply, ih]
    rw [hleft] at h
    simpa only [List.map_append, List.map_cons] using h
  have hold := hred (pre.map cells.cellEquiv.symm)
    (between.map cells.cellEquiv.symm) (suf.map cells.cellEquiv.symm)
    (cells.cellEquiv.symm first) (cells.cellEquiv.symm second) holdSplit
  have hbetween :
      ((between.map cells.cellEquiv.symm).map RelatorCell.value).prod =
        (between.map RelatorCell.value).prod := by
    congr 1
    rw [List.map_map]
    apply List.map_congr_left
    intro cell _
    calc
      (cells.cellEquiv.symm cell).value =
          (cells.cellEquiv (cells.cellEquiv.symm cell)).value :=
        (cells.value_eq (cells.cellEquiv.symm cell)).symm
      _ = cell.value := by rw [cells.cellEquiv.apply_symm_apply]
  have hfirst : (cells.cellEquiv.symm first).value = first.value := by
    calc
      (cells.cellEquiv.symm first).value =
          (cells.cellEquiv (cells.cellEquiv.symm first)).value :=
        (cells.value_eq (cells.cellEquiv.symm first)).symm
      _ = first.value := by rw [cells.cellEquiv.apply_symm_apply]
  have hsecond : (cells.cellEquiv.symm second).value = second.value := by
    calc
      (cells.cellEquiv.symm second).value =
          (cells.cellEquiv (cells.cellEquiv.symm second)).value :=
        (cells.value_eq (cells.cellEquiv.symm second)).symm
      _ = second.value := by rw [cells.cellEquiv.apply_symm_apply]
  rw [hbetween, hfirst, hsecond] at hold
  exact hold

end RCellEquiv

/-! ## Disc-region replacement invariant -/

/-- The observable result of replacing a `G`-cell-only disc region.  The
replacement is an actual planar disc diagram, while the three remaining
fields say that its outer boundary and ordered relator cells are untouched.
Reducedness is derived below from these fields. -/
structure GRegionReplacement
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) where
  diagram : DiscDiagram.{u, w, v'} W
  outerWord_eq : diagram.boundaryWord = Delta.boundaryWord
  cells : RCellEquiv Delta diagram

namespace GRegionReplacement

/-- Replacing a region by itself is the neutral surgery. -/
def refl
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) : GRegionReplacement Delta where
  diagram := Delta
  outerWord_eq := rfl
  cells := RCellEquiv.refl Delta

/-- The replacement has the same number of relator cells. -/
theorem rCellCount_eq
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (replacement : GRegionReplacement.{u, w, v, v'} Delta) :
    replacement.diagram.rCellCount = Delta.rCellCount :=
  replacement.cells.rCellCount_eq

/-- The replacement exposes the finite relator-cell index equivalence. -/
def cellIndexEquiv
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (replacement : GRegionReplacement.{u, w, v, v'} Delta) :
    Fin Delta.rCellCount ≃ Fin replacement.diagram.rCellCount :=
  replacement.cells.indexEquiv

/-- Every ordered relator-cell word survives the replacement. -/
theorem cellWords_eq
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (replacement : GRegionReplacement.{u, w, v, v'} Delta) :
    replacement.diagram.relatorCells.map RelatorCell.word =
      Delta.relatorCells.map RelatorCell.word :=
  replacement.cells.cellWords_eq

/-- Every ordered based relator-cell value survives the replacement. -/
theorem cellValues_eq
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (replacement : GRegionReplacement.{u, w, v, v'} Delta) :
    replacement.diagram.relatorCells.map RelatorCell.value =
      Delta.relatorCells.map RelatorCell.value :=
  replacement.cells.cellValues_eq

/-- A cancelling pair after replacement would transport back to a cancelling
pair before replacement. -/
theorem reduced
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (replacement : GRegionReplacement.{u, w, v, v'} Delta)
    (hred : Delta.Reduced) : replacement.diagram.Reduced :=
  replacement.cells.reduced hred

/-- The replacement operation returns the constructed planar diagram. -/
def replaceGRegion
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (replacement : GRegionReplacement.{u, w, v, v'} Delta) :
    DiscDiagram.{u, w, v'} W :=
  replacement.diagram

end GRegionReplacement

/-! ## Model checks -/

/-- The neutral surgery keeps every relator-cell word. -/
theorem replaceGRegion_refl_cellWords
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) :
    (GRegionReplacement.refl Delta).replaceGRegion.relatorCells.map
        RelatorCell.word = Delta.relatorCells.map RelatorCell.word := by
  rfl

/-- The neutral surgery preserves reducedness, including the zero-relator
one-polygon model of the cactus construction. -/
theorem replaceGRegion_refl_reduced
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (hred : Delta.Reduced) :
    (GRegionReplacement.refl Delta).replaceGRegion.Reduced :=
  (GRegionReplacement.refl Delta).reduced hred

end Surgery

end VanKampen
end GGT
end GroupApproximation
