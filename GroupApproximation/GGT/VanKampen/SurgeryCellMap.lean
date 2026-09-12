import GroupApproximation.GGT.VanKampen.SurgeryOrderedCells

/-!
# Ordered cell maps retaining individual conjugators and orientations

An actual old-to-new map of cell records preserves the listed cells in order.
No bijection of all potential face records is required. The stronger data
transport the ordered O52 certificate as well as words and based values.
-/

namespace GroupApproximation.GGT.VanKampen.Surgery

universe u w v v' v''
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

structure OrderedRCellMap (Delta : DiscDiagram.{u, w, v} W)
    (Xi : DiscDiagram.{u, w, v'} W) (faces : Delta.toCombMap.Face → Xi.toCombMap.Face) where
  cell : RelatorCell Delta.toCombMap Delta.outerFace W → RelatorCell Xi.toCombMap Xi.outerFace W
  face_eq : ∀ C, (cell C).face = faces C.face
  word_eq : ∀ C, (cell C).word = C.word
  conjugator_eq : ∀ C, (cell C).conjugator = C.conjugator
  reversed_eq : ∀ C, (cell C).reversed = C.reversed
  list_eq : Xi.relatorCells = Delta.relatorCells.map cell

namespace OrderedRCellMap

variable {Delta : DiscDiagram.{u, w, v} W} {Xi : DiscDiagram.{u, w, v'} W}
  {Theta : DiscDiagram.{u, w, v''} W}
  {faces : Delta.toCombMap.Face → Xi.toCombMap.Face}
  {nextFaces : Xi.toCombMap.Face → Theta.toCombMap.Face}

def refl (Delta : DiscDiagram.{u, w, v} W) : OrderedRCellMap Delta Delta id where
  cell := id
  face_eq _ := rfl
  word_eq _ := rfl
  conjugator_eq _ := rfl
  reversed_eq _ := rfl
  list_eq := (List.map_id _).symm

def trans (E : OrderedRCellMap Delta Xi faces) (F : OrderedRCellMap Xi Theta nextFaces) :
    OrderedRCellMap Delta Theta (nextFaces ∘ faces) where
  cell := F.cell ∘ E.cell
  face_eq C := (F.face_eq _).trans (congrArg nextFaces (E.face_eq C))
  word_eq C := (F.word_eq _).trans (E.word_eq C)
  conjugator_eq C := (F.conjugator_eq _).trans (E.conjugator_eq C)
  reversed_eq C := (F.reversed_eq _).trans (E.reversed_eq C)
  list_eq := by rw [F.list_eq, E.list_eq, List.map_map]

variable (E : OrderedRCellMap Delta Xi faces)

theorem value_eq (C : RelatorCell Delta.toCombMap Delta.outerFace W) :
    (E.cell C).value = C.value := by
  simp only [RelatorCell.value, E.conjugator_eq, E.reversed_eq, E.word_eq]

theorem map_values (l : List (RelatorCell Delta.toCombMap Delta.outerFace W)) :
    (l.map E.cell).map RelatorCell.value = l.map RelatorCell.value := by
  rw [List.map_map]
  exact List.map_congr_left (fun C _ => E.value_eq C)

include E in
theorem orderedTransport : OrderedRCellTransport Delta Xi := by
  constructor
  · rw [E.list_eq, List.map_map]
    exact List.map_congr_left (fun C _ => E.word_eq C)
  · rw [E.list_eq]; exact E.map_values _

def indexEquiv : Fin Delta.rCellCount ≃ Fin Xi.rCellCount := E.orderedTransport.indexEquiv

theorem indexed_cell (i : Fin Delta.rCellCount) :
    Embedded.cell Xi (E.indexEquiv i) = E.cell (Embedded.cell Delta i) := by
  have h := congrArg (fun l : List (RelatorCell Xi.toCombMap Xi.outerFace W) => l[i.val]?) E.list_eq
  have hXi : i.val < Xi.relatorCells.length := by
    change i.val < Xi.rCellCount
    rw [E.orderedTransport.rCellCount_eq]
    exact i.isLt
  simp only [List.getElem?_map, List.getElem?_eq_getElem hXi,
    List.getElem?_eq_getElem i.isLt, Option.map_some, Option.some.injEq] at h
  exact h

end OrderedRCellMap
end GroupApproximation.GGT.VanKampen.Surgery

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.OrderedRCellMap.trans
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.OrderedRCellMap.orderedTransport
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.OrderedRCellMap.indexed_cell
