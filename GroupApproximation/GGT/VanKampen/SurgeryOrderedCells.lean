import GroupApproximation.GGT.VanKampen.Surgery
import GroupApproximation.GGT.VanKampen.RelativeGreendlinger

/-!
# Transport of the relator cells actually present in a diagram

The historical `RCellEquiv` compares every potential face record. A G-cell
replacement need only preserve the actual ordered lists of words and based
values. These equalities give both O-equivalence and reducedness preservation,
even when the types of unlisted face records change (issue #205).
-/

namespace GroupApproximation.GGT.VanKampen.Surgery

universe u w v v'
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W} {Xi : DiscDiagram.{u, w, v'} W}

/-- Preserve only the actual ordered relator words and based values. -/
structure OrderedRCellTransport (Delta : DiscDiagram.{u, w, v} W)
    (Xi : DiscDiagram.{u, w, v'} W) : Prop where
  words_eq : Xi.relatorCells.map RelatorCell.word = Delta.relatorCells.map RelatorCell.word
  values_eq : Xi.relatorCells.map RelatorCell.value = Delta.relatorCells.map RelatorCell.value

namespace OrderedRCellTransport

theorem refl (Delta : DiscDiagram.{u, w, v} W) : OrderedRCellTransport Delta Delta :=
  ⟨rfl, rfl⟩

theorem of_no_rCells (hDelta : Delta.relatorCells = []) (hXi : Xi.relatorCells = []) :
    OrderedRCellTransport Delta Xi := by
  constructor <;> simp only [hDelta, hXi, List.map_nil]

theorem rCellCount_eq (cells : OrderedRCellTransport Delta Xi) :
    Xi.rCellCount = Delta.rCellCount := by
  have h := congrArg List.length cells.words_eq
  simpa only [List.length_map, DiscDiagram.rCellCount] using h

def indexEquiv (cells : OrderedRCellTransport Delta Xi) :
    Fin Delta.rCellCount ≃ Fin Xi.rCellCount :=
  Fin.castOrderIso cells.rCellCount_eq.symm

theorem cellWord_eq (cells : OrderedRCellTransport Delta Xi) (i : Fin Delta.rCellCount) :
    (Embedded.cell Xi (cells.indexEquiv i)).word = (Embedded.cell Delta i).word := by
  have h := congrArg (fun l : List (List (RelLetter G Lambda)) => l[i.val]?) cells.words_eq
  have hXi : i.val < Xi.relatorCells.length := by
    change i.val < Xi.rCellCount
    rw [cells.rCellCount_eq]
    exact i.isLt
  have hDelta : i.val < Delta.relatorCells.length := i.isLt
  simp only [List.getElem?_map, List.getElem?_eq_getElem hXi,
    List.getElem?_eq_getElem hDelta, Option.map_some, Option.some.injEq] at h
  change (Xi.relatorCells[i.val]).word = (Delta.relatorCells[i.val]).word
  exact h

/-- Any proposed cancelling pair lifts through the equality of value lists. -/
theorem reduced (cells : OrderedRCellTransport Delta Xi) (hred : Delta.Reduced) :
    Xi.Reduced := by
  intro pre between suf first second hsplit
  have hvalues : Delta.relatorCells.map RelatorCell.value =
      pre.map RelatorCell.value ++ first.value ::
        (between.map RelatorCell.value ++ second.value :: suf.map RelatorCell.value) := by
    rw [← cells.values_eq, hsplit, List.map_append, List.map_cons,
      List.map_append, List.map_cons]
  obtain ⟨preOld, rest, hrest, _, hrestmap⟩ := List.map_eq_append_iff.1 hvalues
  obtain ⟨firstOld, rest2, hrest2, hfirst, hrest2map⟩ := List.map_eq_cons_iff.1 hrestmap
  obtain ⟨betweenOld, rest3, hrest3, hbetween, hrest3map⟩ :=
    List.map_eq_append_iff.1 hrest2map
  obtain ⟨secondOld, sufOld, hsuf, hsecond, _⟩ := List.map_eq_cons_iff.1 hrest3map
  have hsplitOld : Delta.relatorCells =
      preOld ++ firstOld :: (betweenOld ++ secondOld :: sufOld) := by
    rw [hrest, hrest2, hrest3, hsuf]
  have h := hred preOld betweenOld sufOld firstOld secondOld hsplitOld
  rwa [hbetween, hfirst, hsecond] at h

end OrderedRCellTransport

/-- The historical stronger interface still maps into the repaired one. -/
theorem RCellEquiv.orderedTransport (cells : RCellEquiv Delta Xi) :
    OrderedRCellTransport Delta Xi := ⟨cells.cellWords_eq, cells.cellValues_eq⟩

/-- A G-region replacement preserving the actual ordered relator cells. -/
structure OrderedGRegionReplacement (Delta : DiscDiagram.{u, w, v} W) where
  diagram : DiscDiagram.{u, w, v'} W
  outerWord_eq : diagram.boundaryWord = Delta.boundaryWord
  cells : OrderedRCellTransport Delta diagram

namespace OrderedGRegionReplacement

def ofHistorical (replacement : GRegionReplacement.{u, w, v, v'} Delta) :
    OrderedGRegionReplacement.{u, w, v, v'} Delta :=
  ⟨replacement.diagram, replacement.outerWord_eq, replacement.cells.orderedTransport⟩

theorem reduced (replacement : OrderedGRegionReplacement.{u, w, v, v'} Delta)
    (hred : Delta.Reduced) : replacement.diagram.Reduced :=
  replacement.cells.reduced hred

/-- The repaired replacement supplies the finite-cell O-equivalence used by
the estimating construction. -/
def oEquivalent (replacement : OrderedGRegionReplacement.{u, w, v, v} Delta) :
    OEquivalentDiscDiagram Delta replacement.diagram where
  boundaryWord_eq := replacement.outerWord_eq
  cellIndex := replacement.cells.indexEquiv
  cellWord_eq := replacement.cells.cellWord_eq

end OrderedGRegionReplacement
end GroupApproximation.GGT.VanKampen.Surgery

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.OrderedRCellTransport.cellWord_eq
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.OrderedRCellTransport.reduced
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.OrderedGRegionReplacement.oEquivalent
