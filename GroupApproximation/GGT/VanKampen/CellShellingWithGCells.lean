import GroupApproximation.GGT.VanKampen.FaceShellingValue
import GroupApproximation.Meta.AxiomGuard

/-!
# Recorded cell shellings with certified G-cell moves

The historical `CellShelling` records every exposed face, so its final walk
can only use darts from the recorded face words. A relator trace alone cannot
account for boundary arcs across intervening G-cells. This replacement keeps
the recorded relator steps and permits actual face-set word homotopies through
null inner faces, including cancellation of adjacent reverse darts.

The extra moves do not add a relator or alter its conjugator. Their word-value
invariance therefore gives exactly the same ordered product formula. The old
predicate remains unchanged and embeds in this one.
-/

namespace GroupApproximation.GGT.VanKampen.Embedded

universe u w v

/-- A recorded shelling may cross null inner faces without recording them as
relator steps. Every such move carries its actual face-set word homotopy. -/
inductive CellShellingWithGCells {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (faces : Finset Delta.toCombMap.Face) :
    List G → List (List Delta.toCombMap.Dart) → List Delta.toCombMap.Dart → Prop
  | empty : CellShellingWithGCells Delta faces [] [] []
  | step {gs : List G} {cds : List (List Delta.toCombMap.Dart)}
      {before arc after exposed : List Delta.toCombMap.Dart}
      (face : Delta.toCombMap.Face) (hface : face ∈ faces) (rev : Bool)
      (k : ℕ) (g : G) (cd : List Delta.toCombMap.Dart)
      (hcd : cd = orientedFaceDarts Delta face rev)
      (hrot : cd.rotate k = exposed ++ invDarts Delta arc)
      (hg : g = shellConjugatorOn Delta cd before k)
      (rest : CellShellingWithGCells Delta faces gs cds (before ++ arc ++ after)) :
      CellShellingWithGCells Delta faces (g :: gs) (cd :: cds)
        (before ++ exposed ++ after)
  | gMove {gs : List G} {cds : List (List Delta.toCombMap.Dart)}
      {first second : List Delta.toCombMap.Dart}
      (gFaces : Finset Delta.toCombMap.Face) (subset : gFaces ⊆ faces)
      (all_gCells : ∀ face ∈ gFaces, face ≠ Delta.outerFace ∧
        RelLetter.listVal (Delta.faceWord face) = 1)
      (move : FaceSetWordHomotopy Delta gFaces first second)
      (rest : CellShellingWithGCells Delta faces gs cds first) :
      CellShellingWithGCells Delta faces gs cds second

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}
  {faces : Finset Delta.toCombMap.Face}
  {gs : List G} {cds : List (List Delta.toCombMap.Dart)}
  {walk : List Delta.toCombMap.Dart}

/-- Every historical recorded shelling remains available. -/
theorem CellShelling.withGCells (h : CellShelling Delta faces gs cds walk) :
    CellShellingWithGCells Delta faces gs cds walk := by
  induction h with
  | empty => exact .empty
  | step face hface rev k g cd hcd hrot hg rest ih =>
      exact .step face hface rev k g cd hcd hrot hg ih

/-- The trace has one conjugator for each recorded face word. -/
theorem CellShellingWithGCells.length_eq
    (h : CellShellingWithGCells Delta faces gs cds walk) : gs.length = cds.length := by
  induction h with
  | empty => rfl
  | step _ _ _ _ _ _ _ _ _ _ ih => simpa only [List.length_cons] using congrArg Nat.succ ih
  | gMove _ _ _ _ _ ih => exact ih

/-- G-cell moves and reverse-pair cancellations preserve the ordered product
of the recorded conjugated face values. -/
theorem listVal_dartWord_of_cellShellingWithGCells
    (h : CellShellingWithGCells Delta faces gs cds walk) :
    RelLetter.listVal (dartWord Delta walk) =
      (List.zipWith (fun g cd => g * RelLetter.listVal (dartWord Delta cd) * g⁻¹)
        gs cds).prod := by
  induction h with
  | empty => rfl
  | @step gs cds before arc after exposed face hface rev k g cd hcd hrot hg rest ih =>
      rw [List.zipWith_cons_cons, List.prod_cons, ← ih, hg]
      exact listVal_dartWord_shellStepOn Delta cd before arc after exposed k hrot
  | gMove gFaces subset all_gCells move rest ih =>
      exact (listVal_dartWord_eq_of_faceSetWordHomotopy Delta gFaces all_gCells move).symm.trans ih

end GroupApproximation.GGT.VanKampen.Embedded

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CellShelling.withGCells
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CellShellingWithGCells.length_eq
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.listVal_dartWord_of_cellShellingWithGCells
