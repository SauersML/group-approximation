import GroupApproximation.GGT.VanKampen.DartExpansion
import GroupApproximation.GGT.VanKampen.SurgeryOrderedCells

/-!
# Composable actual disc subdivisions

The data retain every old face, the exact expanded boundary traversals, the
exterior word, and the actual ordered relator words, values and face indices.
Composition concatenates actual dart expansions and transports those lists.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v v' v''
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

structure DiscExpansion (Delta : DiscDiagram.{u, w, v} W)
    (Xi : DiscDiagram.{u, w, v'} W) extends DartExpansion Delta.toCombMap Xi.toCombMap where
  faceEquiv : Delta.toCombMap.Face ≃ Xi.toCombMap.Face
  boundary_darts : ∀ f, (Xi.faceBoundary (faceEquiv f)).darts =
    (Delta.faceBoundary f).darts.flatMap darts
  outerFace_eq : Xi.outerFace = faceEquiv Delta.outerFace
  outerWord_eq : Xi.boundaryWord = Delta.boundaryWord
  cells : Surgery.OrderedRCellTransport Delta Xi
  cellFaces_eq : Xi.relatorCells.map RelatorCell.face =
    (Delta.relatorCells.map RelatorCell.face).map faceEquiv

namespace DiscExpansion

variable {Delta : DiscDiagram.{u, w, v} W} {Xi : DiscDiagram.{u, w, v'} W}
  {Theta : DiscDiagram.{u, w, v''} W}

def refl (Delta : DiscDiagram.{u, w, v} W) : DiscExpansion Delta Delta where
  toDartExpansion := DartExpansion.refl Delta.toCombMap
  faceEquiv := Equiv.refl _
  boundary_darts f := by
    change (Delta.faceBoundary f).darts = (Delta.faceBoundary f).darts.flatMap (fun d => [d])
    exact (List.flatMap_singleton' _).symm
  outerFace_eq := rfl
  outerWord_eq := rfl
  cells := Surgery.OrderedRCellTransport.refl Delta
  cellFaces_eq := by
    change Delta.relatorCells.map RelatorCell.face = (Delta.relatorCells.map RelatorCell.face).map id
    exact (List.map_id _).symm

def trans (E : DiscExpansion Delta Xi) (F : DiscExpansion Xi Theta) : DiscExpansion Delta Theta where
  toDartExpansion := E.toDartExpansion.trans F.toDartExpansion
  faceEquiv := E.faceEquiv.trans F.faceEquiv
  boundary_darts f := by
    change (Theta.faceBoundary (F.faceEquiv (E.faceEquiv f))).darts =
      (Delta.faceBoundary f).darts.flatMap (fun d => (E.darts d).flatMap F.darts)
    rw [F.boundary_darts, E.boundary_darts, List.flatMap_assoc]
  outerFace_eq := F.outerFace_eq.trans (congrArg F.faceEquiv E.outerFace_eq)
  outerWord_eq := F.outerWord_eq.trans E.outerWord_eq
  cells := ⟨F.cells.words_eq.trans E.cells.words_eq, F.cells.values_eq.trans E.cells.values_eq⟩
  cellFaces_eq := by
    rw [F.cellFaces_eq, E.cellFaces_eq, List.map_map]
    rfl

def replacement (E : DiscExpansion Delta Xi) : Surgery.OrderedGRegionReplacement.{u, w, v, v'} Delta :=
  ⟨Xi, E.outerWord_eq, E.cells⟩

/-- Each expanded dart really remains in the corresponding old face. -/
theorem faceOf_mem (E : DiscExpansion Delta Xi) (d : Delta.toCombMap.Dart)
    (x : Xi.toCombMap.Dart) (hx : x ∈ E.darts d) :
    Xi.toCombMap.faceOf x = E.faceEquiv (Delta.toCombMap.faceOf d) := by
  apply ((Xi.faceBoundary (E.faceEquiv (Delta.toCombMap.faceOf d))).mem_iff x).mp
  rw [E.boundary_darts]
  exact List.mem_flatMap.mpr ⟨d, ((Delta.faceBoundary (Delta.toCombMap.faceOf d)).mem_iff d).mpr rfl, hx⟩

end DiscExpansion
end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.DiscExpansion.trans
#audit_axioms GroupApproximation.GGT.VanKampen.DiscExpansion.faceOf_mem
