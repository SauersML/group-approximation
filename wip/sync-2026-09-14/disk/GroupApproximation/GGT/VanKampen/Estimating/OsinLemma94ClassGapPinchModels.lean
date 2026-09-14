import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketDiscMerge
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchedTwoGonRegion
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSections
import GroupApproximation.Meta.AxiomGuard

/-!
# The pinched collapse at a gap: calibration models

Model tests for the pinched collapse as a producer of `OsinLemma94ClassCaseGapSpanStatement` (Osin,
arXiv:math/0411039v3, §9, proof of Lemma 9.4, Case 1, on class words).  A class of `OsinLemma94ClassPolygons` is an
arc of a relator cell `Π` read from across, gaps included.  The polygon face passes straight across a gap at one
vertex, while `Π` runs round the gap loop.  The producer would collapse the polygon face with the faces behind the gap
(`Surgery.InnerDiscRegion.ofPocketRegion`), so that the class arc is one stretch of the merged face.

Both models use one map with twelve darts.  Its faces are `Π = [0,1,2,3,4]`, the polygon face `F = [8,5,9]`, and the
digons `[7,6]` and `[10,11]`.  The class arc of `Π` over `[0,1,2,3]` reads `[8,7,6,5]` from across: the sides `[8]`
and `[5]` of `F`, and the gap `[7,6]` between them, whose digon meets `F` only at the vertex of the darts `1,3,5,7`.

* **Hair gap** (`hairDiagram`).  The digon `[7,6]` is the G-cell that doubling puts on a hair of `Π`, and `[10,11]`
  is the exterior.  The face set `{F, [7,6]}` is a pocket region (`pocket`).  Reclosing along `[8,7,6,5,9]` splits the
  pinch vertex, giving 5 vertices, 6 edges and 3 faces (`innerMap_euler`).  The complement `{Π, exterior}` recloses
  along `[11,0,1,2,3]` with 4 vertices, 5 edges and 3 faces (`outerMap_euler`).  The merged face of the collapse
  (`discRegion`) reads the class arc as one stretch (`merged_darts`).
* **Gap along `∂Δ`** (`boundaryDiagram`).  The same map, with `[7,6]` the exterior and `[10,11]` a second relator cell.
  The face behind the gap is the exterior, so no pocket region holds it (`gap_face_not_mem`).  The boundary reads `1`
  while the diagram has two relator cells, so the diagram is not least area (`not_leastArea`).  The hypotheses
  `Delta.LeastArea` and `0 < Delta.rCellCount` of the statement fail together here, and its conclusion holds
  vacuously: the collapse fails on this configuration, the statement does not.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 9.4 inside the proof of Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.OsinLemma94GapPinchModel

open Equiv GroupApproximation.HullSC
open Surgery.MapCollapse (InternalDart IsBoundaryDart KeptDart BoundaryCycle IsDiscRegion
  reclosedMap reclosedMap_facePerm_val_of_mem reclosedMap_facePerm_val_of_notMem
  reclosedMap_faceCount reclosedMap_connected)

/-! ## The map -/

def alpha : Perm (Fin 12) where
  toFun := ![5, 6, 7, 8, 10, 0, 1, 2, 3, 11, 4, 9]
  invFun := ![5, 6, 7, 8, 10, 0, 1, 2, 3, 11, 4, 9]
  left_inv := by decide
  right_inv := by decide

def facePerm : Perm (Fin 12) where
  toFun := ![1, 2, 3, 4, 0, 9, 7, 6, 5, 8, 11, 10]
  invFun := ![4, 0, 1, 2, 3, 8, 7, 6, 9, 5, 11, 10]
  left_inv := by decide
  right_inv := by decide

def M : CombMap where
  Dart := Fin 12
  dartFintype := inferInstance
  alpha := alpha
  sigma := facePerm * alpha
  alpha_involutive := by intro d; fin_cases d <;> rfl
  alpha_fixedPointFree := by decide

instance : DecidableEq M.Dart := inferInstanceAs (DecidableEq (Fin 12))
instance (n : ℕ) : OfNat M.Dart n := inferInstanceAs (OfNat (Fin 12) n)

def faceClass : Fin 12 → Fin 4 := ![0, 0, 0, 0, 0, 1, 2, 2, 1, 1, 3, 3]
def faceRep : Fin 4 → Fin 12 := ![0, 8, 7, 10]

noncomputable def faceEquiv : M.Face ≃ Fin 4 :=
  OrbitClassifier.orbitEquiv M.facePerm faceClass faceRep
    (by decide) (by decide) (by decide)

def face (i : Fin 4) : M.Face := M.faceOf (faceRep i)

@[simp] theorem faceEquiv_face (i : Fin 4) : faceEquiv (face i) = i := by
  change faceClass (faceRep i) = i
  fin_cases i <;> rfl

theorem faceOf_eq_face (d : Fin 12) (i : Fin 4) :
    M.faceOf d = face i ↔ faceClass d = i := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face]
  rfl

theorem face_eq_iff (i j : Fin 4) : face i = face j ↔ i = j := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face, faceEquiv_face]

noncomputable def vertexEquiv : M.Vertex ≃ Fin 4 :=
  OrbitClassifier.orbitEquiv M.sigma (![0, 1, 2, 1, 3, 1, 2, 1, 3, 0, 0, 3] : Fin 12 → Fin 4)
    (![0, 1, 2, 4] : Fin 4 → Fin 12) (by decide) (by decide) (by decide)

theorem planar : M.IsPlanar := by
  constructor
  · have hstep : ∀ d : Fin 12, Relation.EqvGen M.Adjacent 0 d := by
      have trans {d e f : M.Dart}
          (hde : Relation.EqvGen M.Adjacent d e)
          (hef : Relation.EqvGen M.Adjacent e f) :
          Relation.EqvGen M.Adjacent d f := .trans _ _ _ hde hef
      have h05 : Relation.EqvGen M.Adjacent 0 5 := .rel _ _ (Or.inl rfl)
      have h51 : Relation.EqvGen M.Adjacent 5 1 := .rel _ _ (Or.inr rfl)
      have h16 : Relation.EqvGen M.Adjacent 1 6 := .rel _ _ (Or.inl rfl)
      have h62 : Relation.EqvGen M.Adjacent 6 2 := .rel _ _ (Or.inr rfl)
      have h17 : Relation.EqvGen M.Adjacent 1 7 := .rel _ _ (Or.inr rfl)
      have h09 : Relation.EqvGen M.Adjacent 0 9 := .rel _ _ (Or.inr rfl)
      have h910 : Relation.EqvGen M.Adjacent 9 10 := .rel _ _ (Or.inr rfl)
      have h104 : Relation.EqvGen M.Adjacent 10 4 := .rel _ _ (Or.inl rfl)
      have h411 : Relation.EqvGen M.Adjacent 4 11 := .rel _ _ (Or.inr rfl)
      have h118 : Relation.EqvGen M.Adjacent 11 8 := .rel _ _ (Or.inr rfl)
      have h83 : Relation.EqvGen M.Adjacent 8 3 := .rel _ _ (Or.inl rfl)
      have h04 : Relation.EqvGen M.Adjacent 0 4 := trans (trans h09 h910) h104
      have h08 : Relation.EqvGen M.Adjacent 0 8 := trans (trans h04 h411) h118
      intro d
      fin_cases d
      · exact .refl _
      · exact trans h05 h51
      · exact trans (trans (trans h05 h51) h16) h62
      · exact trans h08 h83
      · exact h04
      · exact h05
      · exact trans (trans h05 h51) h16
      · exact trans (trans h05 h51) h17
      · exact h08
      · exact h09
      · exact trans h09 h910
      · exact trans h04 h411
    intro d e
    exact .trans _ _ _ (.symm _ _ (hstep d)) (hstep e)
  · have hv : M.vertexCount = 4 := (Nat.card_congr vertexEquiv).trans (by simp)
    have hf : M.faceCount = 4 := (Nat.card_congr faceEquiv).trans (by simp)
    have hd : M.dartCount = 12 := by simp [CombMap.dartCount, M]
    have he := M.dartCount_eq_two_mul_edgeCount
    unfold CombMap.eulerCharacteristic
    rw [hv, hf]
    have heq : M.edgeCount = 6 := by omega
    rw [heq]
    norm_num

def faceDarts : Fin 4 → List (Fin 12) := ![[0, 1, 2, 3, 4], [8, 5, 9], [7, 6], [10, 11]]

noncomputable def indexedBoundary (i : Fin 4) : FaceBoundary M (face i) where
  darts := faceDarts i
  nonempty := by change faceDarts i ≠ ([] : List (Fin 12)); fin_cases i <;> decide
  nodup := by fin_cases i <;> decide
  mem_iff := by
    intro d
    rw [faceOf_eq_face]
    fin_cases i <;> fin_cases d <;> decide
  chain := by fin_cases i <;> decide
  closes := by fin_cases i <;> decide
  length_eq_degree := by
    have h := closedOrbitList.length_eq_orbitDegree M.facePerm (faceRep i)
    have hd : closedOrbitList M.facePerm (faceRep i) = faceDarts i := by
      fin_cases i <;> decide
    rw [hd] at h
    exact h

noncomputable def boundary (f : M.Face) : FaceBoundary M f :=
  (faceEquiv.left_inv f) ▸ indexedBoundary (faceEquiv f)

@[simp] theorem boundary_face_darts (i : Fin 4) :
    (boundary (face i)).darts = faceDarts i := by
  have htransport {f g : M.Face} (h : f = g) (B : FaceBoundary M f) :
      (h ▸ B).darts = B.darts := by cases h; rfl
  unfold boundary
  rw [htransport]
  exact congrArg faceDarts (faceEquiv_face i)

/-- The polygon face and the digon `[7,6]` share no edge, and meet at the vertex of the darts `5` and `7`. -/
theorem pinch_noEdge : ∀ d : Fin 12, faceClass d = 1 → faceClass (M.alpha d) ≠ 2 := by
  decide

theorem pinch_vertex : M.vertexOf (5 : Fin 12) = M.vertexOf (7 : Fin 12) :=
  vertexEquiv.injective (by decide)

/-! ## The labels -/

abbrev G := Perm (Fin 3)

def gx : G := Equiv.swap 0 1
def gy : G := Equiv.swap 1 2
def gz : G := Equiv.swap 0 2

/-- `Π` reads `x y y⁻¹ z (x z)`, `F` reads `z⁻¹ x⁻¹ (x z)`, the digon `[7,6]` reads `y y⁻¹`, and the digon
`[10,11]` reads `(x z)⁻¹ (x z)⁻¹`. -/
def label (d : Fin 12) : RelLetter G Empty :=
  .base ((![gx, gy, gy⁻¹, gz, gx * gz, gx⁻¹, gy⁻¹, gy, gz⁻¹, gx * gz, (gx * gz)⁻¹, (gx * gz)⁻¹] :
    Fin 12 → G) d)

theorem label_alpha (d : M.Dart) : label (M.alpha d) = RelWord.inv (label d) := by
  fin_cases d <;> exact congrArg RelLetter.base (by decide)

def relator : List (RelLetter G Empty) :=
  [.base gx, .base gy, .base gy⁻¹, .base gz, .base (gx * gz)]

def relatorTwo : List (RelLetter G Empty) := [.base (gx * gz)⁻¹, .base (gx * gz)⁻¹]

/-! ## The hair diagram -/

def hairW : Set (List (RelLetter G Empty)) := {relator}

def hairCell : RelatorCell M (face 3) hairW where
  face := face 0
  face_ne_outer := (face_eq_iff 0 3).not.mpr (by decide)
  word := relator
  word_mem := rfl
  conjugator := 1
  reversed := false

/-- **The hair diagram**: `[7,6]` is the G-digon on a doubled hair of `Π`, and `[10,11]` is the exterior. -/
noncomputable def hairDiagram : DiscDiagram hairW where
  toCombMap := M
  planar := planar
  label := label
  label_alpha := label_alpha
  outerFace := face 3
  faceBoundary := boundary
  relatorCells := [hairCell]
  relatorCell_faces_nodup := by simp
  relatorCell_word := by
    intro C hC
    have h : C = hairCell := List.mem_singleton.mp hC
    subst C
    change relator = (boundary (face 0)).darts.map label
    rw [boundary_face_darts]
    rfl
  inner_face := by
    intro f hf
    obtain ⟨i, rfl⟩ : ∃ i, face i = f := ⟨faceEquiv f, faceEquiv.left_inv f⟩
    fin_cases i
    · exact Or.inl ⟨hairCell, List.mem_singleton_self _, rfl⟩
    · right
      rw [boundary_face_darts]
      decide
    · right
      rw [boundary_face_darts]
      decide
    · exact (hf rfl).elim
  boundary_product := by
    rw [boundary_face_darts]
    decide

instance : NeZero hairDiagram.rCellCount := ⟨by decide⟩
instance (n : ℕ) : OfNat hairDiagram.toCombMap.Dart n := inferInstanceAs (OfNat (Fin 12) n)
instance : DecidableEq hairDiagram.toCombMap.Dart := inferInstanceAs (DecidableEq (Fin 12))

@[simp] theorem hairDiagram_cellDarts : Embedded.cellDarts hairDiagram 0 = [0, 1, 2, 3, 4] := by
  change (boundary (face 0)).darts = _
  rw [boundary_face_darts]
  rfl

/-- The class arc of `Π` over `[0,1,2,3]`. -/
def classArc : Embedded.CyclicArc (Embedded.cellDarts hairDiagram 0) where
  start := ⟨0, Nat.succ_pos _⟩
  length := 4
  length_le := by
    rw [hairDiagram_cellDarts]
    decide

theorem classArc_darts : classArc.darts = [0, 1, 2, 3] := by
  change ((Embedded.cellDarts hairDiagram 0).drop 0 ++
    (Embedded.cellDarts hairDiagram 0).take 0).take 4 = _
  rw [hairDiagram_cellDarts]
  rfl

/-- **The class arc from across**: the side `[8]`, the gap `[7,6]`, and the side `[5]`. -/
theorem classArc_reverseDarts : classArc.reverseDarts = [8, 7, 6, 5] := by
  change classArc.darts.reverse.map hairDiagram.toCombMap.alpha = _
  rw [classArc_darts]
  rfl

/-- The gap reads `1`. -/
theorem gap_value : RelLetter.listVal (Embedded.dartWord hairDiagram [7, 6]) = 1 := by
  decide

/-! ## The gap along `∂Δ` -/

def boundaryW : Set (List (RelLetter G Empty)) := {relator, relatorTwo}

def boundaryCell : RelatorCell M (face 2) boundaryW where
  face := face 0
  face_ne_outer := (face_eq_iff 0 2).not.mpr (by decide)
  word := relator
  word_mem := Or.inl rfl
  conjugator := 1
  reversed := false

def boundaryCellTwo : RelatorCell M (face 2) boundaryW where
  face := face 3
  face_ne_outer := (face_eq_iff 3 2).not.mpr (by decide)
  word := relatorTwo
  word_mem := Or.inr rfl
  conjugator := 1
  reversed := false

/-- **The boundary diagram**: `[7,6]` is the exterior, and `[10,11]` is a second relator cell. -/
noncomputable def boundaryDiagram : DiscDiagram boundaryW where
  toCombMap := M
  planar := planar
  label := label
  label_alpha := label_alpha
  outerFace := face 2
  faceBoundary := boundary
  relatorCells := [boundaryCell, boundaryCellTwo]
  relatorCell_faces_nodup := by
    change [face 0, face 3].Nodup
    refine List.nodup_cons.mpr ⟨fun h => ?_, List.nodup_singleton _⟩
    exact absurd ((face_eq_iff 0 3).mp (List.mem_singleton.mp h)) (by decide)
  relatorCell_word := by
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · change relator = (boundary (face 0)).darts.map label
      rw [boundary_face_darts]
      rfl
    · obtain rfl := List.mem_singleton.mp hC
      change relatorTwo = (boundary (face 3)).darts.map label
      rw [boundary_face_darts]
      rfl
  inner_face := by
    intro f hf
    obtain ⟨i, rfl⟩ : ∃ i, face i = f := ⟨faceEquiv f, faceEquiv.left_inv f⟩
    fin_cases i
    · exact Or.inl ⟨boundaryCell, by simp, rfl⟩
    · right
      rw [boundary_face_darts]
      decide
    · exact (hf rfl).elim
    · exact Or.inl ⟨boundaryCellTwo, by simp, rfl⟩
  boundary_product := by
    rw [boundary_face_darts]
    decide

instance : NeZero boundaryDiagram.rCellCount := ⟨by decide⟩

/-- **The face behind the gap is the exterior**, so no pocket region holds it. -/
theorem gap_face_not_mem (P : PocketRegion boundaryDiagram) :
    boundaryDiagram.toCombMap.faceOf (7 : Fin 12) ∉ P.faces := by
  have h : boundaryDiagram.toCombMap.faceOf (7 : Fin 12) = boundaryDiagram.outerFace :=
    (faceOf_eq_face 7 2).mpr rfl
  rw [h]
  exact P.outerFace_not_mem

theorem boundaryValue_eq_one : boundaryDiagram.boundaryValue = 1 := by
  change RelLetter.listVal (RelWord.revInv ((boundary (face 2)).darts.map label)) = 1
  rw [boundary_face_darts]
  decide

/-- **The boundary model is not least area**: its boundary reads `1`, a product of no relators, and it has two
relator cells. -/
theorem not_leastArea : ¬ boundaryDiagram.LeastArea := by
  intro h
  have hle := h (m := 0) (by
    rw [boundaryValue_eq_one]
    exact RelatorDefectBudget.IsRelatorProduct.one)
  exact absurd hle (by decide)

/-! ## The hair gap: a pocket region -/

/-- The polygon face and the digon behind the gap. -/
def pinchFaces : Finset hairDiagram.toCombMap.Face :=
  Finset.cons (face 1) {face 2} fun h =>
    absurd ((face_eq_iff 1 2).mp (Finset.mem_singleton.mp h)) (by decide)

theorem mem_pinchFaces_iff (x : Fin 12) :
    hairDiagram.toCombMap.faceOf x ∈ pinchFaces ↔ faceClass x = 1 ∨ faceClass x = 2 :=
  Finset.mem_cons.trans (or_congr (faceOf_eq_face x 1)
    (Finset.mem_singleton.trans (faceOf_eq_face x 2)))

theorem innerBoundaryDart_iff (d : Fin 12) :
    IsBoundaryDart hairDiagram.toCombMap pinchFaces d ↔ d ∈ ([8, 7, 6, 5, 9] : List (Fin 12)) := by
  change (M.faceOf d ∈ Finset.cons (face 1) {face 2} _ ∧
    M.faceOf (M.alpha d) ∉ Finset.cons (face 1) {face 2} _) ↔ _
  simp only [Finset.mem_cons, Finset.mem_singleton, faceOf_eq_face]
  fin_cases d <;> decide

theorem not_internalDart_pinch (d : Fin 12) : ¬ InternalDart hairDiagram.toCombMap pinchFaces d := by
  rintro ⟨hd, hα⟩
  change M.faceOf d ∈ Finset.cons (face 1) {face 2} _ at hd
  change M.faceOf (M.alpha d) ∈ Finset.cons (face 1) {face 2} _ at hα
  simp only [Finset.mem_cons, Finset.mem_singleton, faceOf_eq_face] at hd hα
  revert hd hα
  fin_cases d <;> decide

/-- The boundary darts of the pocket in the order of the merged face: `F` up to the pinch, the digon, the rest of
`F`. -/
def innerCycle : BoundaryCycle hairDiagram.toCombMap pinchFaces where
  cycle := ([8, 7, 6, 5, 9] : List (Fin 12))
  cycle_nonempty := List.cons_ne_nil _ _
  cycle_nodup := (by decide : ([8, 7, 6, 5, 9] : List (Fin 12)).Nodup)
  cycle_mem_iff := fun d => (innerBoundaryDart_iff d).symm

/-- The face rotation of the reclosed pocket, on the ambient darts. -/
def innerRot : Fin 12 → Fin 12 := ![1, 2, 3, 4, 0, 9, 5, 6, 7, 8, 11, 10]

/-- The vertex rotation of the reclosed pocket, on the ambient darts. -/
def innerVertexRot : Perm (Fin 12) where
  toFun := ![9, 5, 6, 7, 11, 1, 2, 3, 4, 10, 0, 8]
  invFun := ![10, 5, 6, 7, 8, 1, 2, 3, 11, 0, 9, 4]
  left_inv := by decide
  right_inv := by decide

theorem innerCycle_next :
    ∀ (x : Fin 12) (hx : x ∈ ([8, 7, 6, 5, 9] : List (Fin 12))),
      List.next [8, 7, 6, 5, 9] x hx = innerRot x := by
  decide

theorem innerRot_of_not_mem :
    ∀ x : Fin 12, ¬(faceClass x = 1 ∨ faceClass x = 2) → M.facePerm x = innerRot x := by
  decide

theorem innerRot_alpha : ∀ x : Fin 12, innerRot (M.alpha x) = innerVertexRot x := by
  decide

theorem innerRot_val (e : KeptDart hairDiagram.toCombMap pinchFaces) :
    ((reclosedMap hairDiagram.toCombMap pinchFaces innerCycle).facePerm e).1 = innerRot e.1 := by
  obtain ⟨x, hx⟩ := e
  by_cases h : hairDiagram.toCombMap.faceOf x ∈ pinchFaces
  · rw [reclosedMap_facePerm_val_of_mem hairDiagram.toCombMap pinchFaces innerCycle ⟨x, hx⟩ h,
      Surgery.MapCollapse.BoundaryCycle.boundaryPerm_apply_val]
    exact innerCycle_next x _
  · rw [reclosedMap_facePerm_val_of_notMem hairDiagram.toCombMap pinchFaces innerCycle ⟨x, hx⟩ h]
    exact innerRot_of_not_mem x ((mem_pinchFaces_iff x).not.mp h)

theorem innerVertexRot_val (d : KeptDart hairDiagram.toCombMap pinchFaces) :
    ((reclosedMap hairDiagram.toCombMap pinchFaces innerCycle).sigma d).1 = innerVertexRot d.1 := by
  have hs : (reclosedMap hairDiagram.toCombMap pinchFaces innerCycle).facePerm
      ((reclosedMap hairDiagram.toCombMap pinchFaces innerCycle).alpha d) =
      (reclosedMap hairDiagram.toCombMap pinchFaces innerCycle).sigma d := by
    change (reclosedMap hairDiagram.toCombMap pinchFaces innerCycle).sigma
      ((reclosedMap hairDiagram.toCombMap pinchFaces innerCycle).alpha
        ((reclosedMap hairDiagram.toCombMap pinchFaces innerCycle).alpha d)) = _
    rw [(reclosedMap hairDiagram.toCombMap pinchFaces innerCycle).alpha_involutive]
  rw [← hs, innerRot_val]
  exact innerRot_alpha d.1

def innerVertexClass : Fin 12 → Fin 5 := ![0, 1, 2, 3, 4, 1, 2, 3, 4, 0, 0, 4]
def innerVertexRep : Fin 5 → Fin 12 := ![0, 1, 2, 3, 4]

theorem innerVertexClass_rot :
    ∀ x : Fin 12, innerVertexClass (innerVertexRot x) = innerVertexClass x := by
  decide

theorem innerVertexClass_rep : ∀ i : Fin 5, innerVertexClass (innerVertexRep i) = i := by
  decide

theorem innerVertexRot_sameCycle :
    ∀ x : Fin 12, innerVertexRot.SameCycle (innerVertexRep (innerVertexClass x)) x := by
  decide

/-- The vertices of the reclosed pocket: the pinch vertex splits into `{1,5}` and `{3,7}`. -/
noncomputable def innerVertexEquiv :
    (reclosedMap hairDiagram.toCombMap pinchFaces innerCycle).Vertex ≃ Fin 5 :=
  OrbitClassifier.orbitEquiv (reclosedMap hairDiagram.toCombMap pinchFaces innerCycle).sigma
    (fun d : KeptDart hairDiagram.toCombMap pinchFaces => innerVertexClass d.1)
    (fun i => (⟨innerVertexRep i, not_internalDart_pinch _⟩ :
      KeptDart hairDiagram.toCombMap pinchFaces))
    (fun d => (congrArg innerVertexClass (innerVertexRot_val d)).trans
      (innerVertexClass_rot d.1))
    (fun i => innerVertexClass_rep i)
    (fun d => OsinPocketPinchedTwoGonModel.sameCycle_of_val
      (reclosedMap hairDiagram.toCombMap pinchFaces innerCycle).sigma
      innerVertexRot innerVertexRot_val
      ⟨innerVertexRep (innerVertexClass d.1), not_internalDart_pinch _⟩ d
      (innerVertexRot_sameCycle d.1))

theorem innerMap_vertexCount :
    (reclosedMap hairDiagram.toCombMap pinchFaces innerCycle).vertexCount = 5 :=
  (Nat.card_congr innerVertexEquiv).trans (by simp)

theorem innerMap_dartCount :
    (reclosedMap hairDiagram.toCombMap pinchFaces innerCycle).dartCount = 12 :=
  (Nat.card_congr (Equiv.subtypeUnivEquiv not_internalDart_pinch)).trans (by simp)

theorem pinchFaces_card : pinchFaces.card = 1 + 1 :=
  (Finset.card_cons _).trans (congrArg (· + 1) (Finset.card_singleton _))

theorem innerMap_euler :
    (reclosedMap hairDiagram.toCombMap pinchFaces innerCycle).eulerCharacteristic =
      hairDiagram.toCombMap.eulerCharacteristic := by
  have hE :=
    (reclosedMap hairDiagram.toCombMap pinchFaces innerCycle).dartCount_eq_two_mul_edgeCount
  rw [innerMap_dartCount] at hE
  have hF := reclosedMap_faceCount hairDiagram.toCombMap pinchFaces innerCycle
  have hF0 : hairDiagram.toCombMap.faceCount = 4 := (Nat.card_congr faceEquiv).trans (by simp)
  rw [pinchFaces_card, hF0] at hF
  have hE6 : (reclosedMap hairDiagram.toCombMap pinchFaces innerCycle).edgeCount = 6 := by omega
  have hF3 : (reclosedMap hairDiagram.toCombMap pinchFaces innerCycle).faceCount = 3 := by omega
  have h2 : hairDiagram.toCombMap.eulerCharacteristic = 2 := hairDiagram.planar.2
  rw [h2]
  unfold CombMap.eulerCharacteristic
  rw [innerMap_vertexCount, hE6, hF3]
  norm_num

/-- **The pocket is a disc region**, although its two faces meet only at the pinch vertex. -/
noncomputable def innerRegion : IsDiscRegion hairDiagram.toCombMap pinchFaces where
  toBoundaryCycle := innerCycle
  reclosed_connected := reclosedMap_connected _ _ innerCycle hairDiagram.planar.1
  euler_preserved := innerMap_euler

/-! ## The hair gap: the complement -/

/-- The relator cell and the exterior face. -/
def outsideFaces : Finset hairDiagram.toCombMap.Face :=
  Finset.cons (face 0) {face 3} fun h =>
    absurd ((face_eq_iff 0 3).mp (Finset.mem_singleton.mp h)) (by decide)

theorem mem_outsideFaces_iff (x : Fin 12) :
    hairDiagram.toCombMap.faceOf x ∈ outsideFaces ↔ faceClass x = 0 ∨ faceClass x = 3 :=
  Finset.mem_cons.trans (or_congr (faceOf_eq_face x 0)
    (Finset.mem_singleton.trans (faceOf_eq_face x 3)))

theorem outsideBoundaryDart_iff (d : Fin 12) :
    IsBoundaryDart hairDiagram.toCombMap outsideFaces d ↔ d ∈ ([11, 0, 1, 2, 3] : List (Fin 12)) := by
  change (M.faceOf d ∈ Finset.cons (face 0) {face 3} _ ∧
    M.faceOf (M.alpha d) ∉ Finset.cons (face 0) {face 3} _) ↔ _
  simp only [Finset.mem_cons, Finset.mem_singleton, faceOf_eq_face]
  fin_cases d <;> decide

theorem internalDart_outside_iff (d : Fin 12) :
    InternalDart hairDiagram.toCombMap outsideFaces d ↔ d = 4 ∨ d = 10 := by
  change (M.faceOf d ∈ Finset.cons (face 0) {face 3} _ ∧
    M.faceOf (M.alpha d) ∈ Finset.cons (face 0) {face 3} _) ↔ _
  simp only [Finset.mem_cons, Finset.mem_singleton, faceOf_eq_face]
  fin_cases d <;> decide

/-- The boundary darts of the complement: the other sides of the five edges of the pocket. -/
def outerCycle : BoundaryCycle hairDiagram.toCombMap outsideFaces where
  cycle := ([11, 0, 1, 2, 3] : List (Fin 12))
  cycle_nonempty := List.cons_ne_nil _ _
  cycle_nodup := (by decide : ([11, 0, 1, 2, 3] : List (Fin 12)).Nodup)
  cycle_mem_iff := fun d => (outsideBoundaryDart_iff d).symm

/-- The face rotation of the reclosed complement, on the ambient darts (`4` and `10` are deleted). -/
def outerRot : Fin 12 → Fin 12 := ![1, 2, 3, 11, 4, 9, 7, 6, 5, 8, 10, 0]

/-- The vertex rotation of the reclosed complement, on the ambient darts. -/
def outerVertexRot : Perm (Fin 12) where
  toFun := ![9, 7, 6, 5, 10, 1, 2, 3, 11, 0, 4, 8]
  invFun := ![9, 5, 6, 7, 10, 3, 2, 1, 11, 0, 4, 8]
  left_inv := by decide
  right_inv := by decide

theorem outerCycle_next :
    ∀ (x : Fin 12) (hx : x ∈ ([11, 0, 1, 2, 3] : List (Fin 12))),
      List.next [11, 0, 1, 2, 3] x hx = outerRot x := by
  decide

theorem outerRot_of_not_mem :
    ∀ x : Fin 12, ¬(faceClass x = 0 ∨ faceClass x = 3) → M.facePerm x = outerRot x := by
  decide

theorem outerRot_alpha : ∀ x : Fin 12, outerRot (M.alpha x) = outerVertexRot x := by
  decide

theorem outerRot_val (e : KeptDart hairDiagram.toCombMap outsideFaces) :
    ((reclosedMap hairDiagram.toCombMap outsideFaces outerCycle).facePerm e).1 = outerRot e.1 := by
  obtain ⟨x, hx⟩ := e
  by_cases h : hairDiagram.toCombMap.faceOf x ∈ outsideFaces
  · rw [reclosedMap_facePerm_val_of_mem hairDiagram.toCombMap outsideFaces outerCycle ⟨x, hx⟩ h,
      Surgery.MapCollapse.BoundaryCycle.boundaryPerm_apply_val]
    exact outerCycle_next x _
  · rw [reclosedMap_facePerm_val_of_notMem hairDiagram.toCombMap outsideFaces outerCycle ⟨x, hx⟩ h]
    exact outerRot_of_not_mem x ((mem_outsideFaces_iff x).not.mp h)

theorem outerVertexRot_val (d : KeptDart hairDiagram.toCombMap outsideFaces) :
    ((reclosedMap hairDiagram.toCombMap outsideFaces outerCycle).sigma d).1 =
      outerVertexRot d.1 := by
  have hs : (reclosedMap hairDiagram.toCombMap outsideFaces outerCycle).facePerm
      ((reclosedMap hairDiagram.toCombMap outsideFaces outerCycle).alpha d) =
      (reclosedMap hairDiagram.toCombMap outsideFaces outerCycle).sigma d := by
    change (reclosedMap hairDiagram.toCombMap outsideFaces outerCycle).sigma
      ((reclosedMap hairDiagram.toCombMap outsideFaces outerCycle).alpha
        ((reclosedMap hairDiagram.toCombMap outsideFaces outerCycle).alpha d)) = _
    rw [(reclosedMap hairDiagram.toCombMap outsideFaces outerCycle).alpha_involutive]
  rw [← hs, outerRot_val]
  exact outerRot_alpha d.1

def outerVertexClass : Fin 12 → Fin 4 := ![0, 1, 2, 1, 0, 1, 2, 1, 3, 0, 0, 3]
def outerVertexRep : Fin 4 → Fin 12 := ![0, 1, 2, 8]

theorem outerVertexClass_rot :
    ∀ x : Fin 12, outerVertexClass (outerVertexRot x) = outerVertexClass x := by
  decide

theorem outerVertexClass_rep : ∀ i : Fin 4, outerVertexClass (outerVertexRep i) = i := by
  decide

theorem outerVertexRot_sameCycle : ∀ x : Fin 12, x ≠ 4 → x ≠ 10 →
    outerVertexRot.SameCycle (outerVertexRep (outerVertexClass x)) x := by
  decide

theorem outerVertexRep_kept (i : Fin 4) :
    ¬ InternalDart hairDiagram.toCombMap outsideFaces (outerVertexRep i) := by
  rw [internalDart_outside_iff]
  fin_cases i <;> decide

theorem ne_four_of_kept (d : KeptDart hairDiagram.toCombMap outsideFaces) : (d.1 : Fin 12) ≠ 4 :=
  fun h => d.2 ((internalDart_outside_iff d.1).mpr (Or.inl h))

theorem ne_ten_of_kept (d : KeptDart hairDiagram.toCombMap outsideFaces) : (d.1 : Fin 12) ≠ 10 :=
  fun h => d.2 ((internalDart_outside_iff d.1).mpr (Or.inr h))

/-- The vertices of the reclosed complement. -/
noncomputable def outerVertexEquiv :
    (reclosedMap hairDiagram.toCombMap outsideFaces outerCycle).Vertex ≃ Fin 4 :=
  OrbitClassifier.orbitEquiv (reclosedMap hairDiagram.toCombMap outsideFaces outerCycle).sigma
    (fun d : KeptDart hairDiagram.toCombMap outsideFaces => outerVertexClass d.1)
    (fun i => (⟨outerVertexRep i, outerVertexRep_kept i⟩ :
      KeptDart hairDiagram.toCombMap outsideFaces))
    (fun d => (congrArg outerVertexClass (outerVertexRot_val d)).trans
      (outerVertexClass_rot d.1))
    (fun i => outerVertexClass_rep i)
    (fun d => OsinPocketPinchedTwoGonModel.sameCycle_of_val
      (reclosedMap hairDiagram.toCombMap outsideFaces outerCycle).sigma
      outerVertexRot outerVertexRot_val
      ⟨outerVertexRep (outerVertexClass d.1), outerVertexRep_kept _⟩ d
      (outerVertexRot_sameCycle d.1 (ne_four_of_kept d) (ne_ten_of_kept d)))

theorem outerMap_vertexCount :
    (reclosedMap hairDiagram.toCombMap outsideFaces outerCycle).vertexCount = 4 :=
  (Nat.card_congr outerVertexEquiv).trans (by simp)

theorem outerMap_dartCount :
    (reclosedMap hairDiagram.toCombMap outsideFaces outerCycle).dartCount = 10 := by
  let e : KeptDart hairDiagram.toCombMap outsideFaces ≃ {d : Fin 12 // ¬(d = 4 ∨ d = 10)} :=
    Equiv.subtypeEquivRight fun d => not_congr (internalDart_outside_iff d)
  have h := Nat.card_congr e
  change Nat.card (KeptDart hairDiagram.toCombMap outsideFaces) = 10
  rw [h, Nat.card_eq_fintype_card]
  decide

theorem outsideFaces_card : outsideFaces.card = 1 + 1 :=
  (Finset.card_cons _).trans (congrArg (· + 1) (Finset.card_singleton _))

theorem outerMap_euler :
    (reclosedMap hairDiagram.toCombMap outsideFaces outerCycle).eulerCharacteristic =
      hairDiagram.toCombMap.eulerCharacteristic := by
  have hE :=
    (reclosedMap hairDiagram.toCombMap outsideFaces outerCycle).dartCount_eq_two_mul_edgeCount
  rw [outerMap_dartCount] at hE
  have hF := reclosedMap_faceCount hairDiagram.toCombMap outsideFaces outerCycle
  have hF0 : hairDiagram.toCombMap.faceCount = 4 := (Nat.card_congr faceEquiv).trans (by simp)
  rw [outsideFaces_card, hF0] at hF
  have hE5 : (reclosedMap hairDiagram.toCombMap outsideFaces outerCycle).edgeCount = 5 := by omega
  have hF3 : (reclosedMap hairDiagram.toCombMap outsideFaces outerCycle).faceCount = 3 := by omega
  have h2 : hairDiagram.toCombMap.eulerCharacteristic = 2 := hairDiagram.planar.2
  rw [h2]
  unfold CombMap.eulerCharacteristic
  rw [outerMap_vertexCount, hE5, hF3]
  norm_num

/-- **The complement is a disc region.** -/
noncomputable def outerRegion : IsDiscRegion hairDiagram.toCombMap outsideFaces where
  toBoundaryCycle := outerCycle
  reclosed_connected := reclosedMap_connected _ _ outerCycle hairDiagram.planar.1
  euler_preserved := outerMap_euler

theorem mem_outsideFaces_iff_not_mem (f : hairDiagram.toCombMap.Face) :
    f ∈ outsideFaces ↔ f ∉ pinchFaces := by
  obtain ⟨i, rfl⟩ : ∃ i, face i = f :=
    ⟨faceEquiv f, faceEquiv.injective (faceEquiv_face (faceEquiv f))⟩
  change face i ∈ Finset.cons (face 0) {face 3} _ ↔ ¬ face i ∈ Finset.cons (face 1) {face 2} _
  simp only [Finset.mem_cons, Finset.mem_singleton, face_eq_iff]
  fin_cases i <;> decide

/-! ## The hair gap: the collapse -/

/-- **The pinched pocket of the hair gap is a pocket region.** -/
noncomputable def pocket : PocketRegion hairDiagram where
  faces := pinchFaces
  outside := outsideFaces
  mem_outside_iff := mem_outsideFaces_iff_not_mem
  outerFace_mem := Finset.mem_cons.mpr (Or.inr (Finset.mem_singleton_self _))
  inner := innerRegion
  outer := outerRegion
  invDarts_outer_rotate := ⟨0, by decide⟩

theorem pocket_cells_avoid : ∀ C ∈ hairDiagram.relatorCells, C.face ∉ pocket.faces := by
  intro C hC
  have h : C = hairCell := List.mem_singleton.mp hC
  subst C
  change face 0 ∉ Finset.cons (face 1) {face 2} _
  simp only [Finset.mem_cons, Finset.mem_singleton, face_eq_iff]
  decide

/-- **The collapse of the pocket.** -/
noncomputable def discRegion : Surgery.InnerDiscRegion hairDiagram :=
  Surgery.InnerDiscRegion.ofPocketRegion pocket pocket_cells_avoid

/-- **The merged face reads the class arc as one stretch**, gaps included, followed by the rest of the polygon
face. -/
theorem merged_darts :
    (discRegion.diagram.faceBoundary discRegion.merged).darts =
      (classArc.reverseDarts ++ [9]).map discRegion.keep := by
  rw [discRegion.faceBoundary_merged_darts_eq_map_keep, classArc_reverseDarts]
  rfl

end GroupApproximation.GGT.VanKampen.OsinLemma94GapPinchModel

#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94GapPinchModel.planar
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94GapPinchModel.classArc_reverseDarts
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94GapPinchModel.innerMap_euler
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94GapPinchModel.outerMap_euler
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94GapPinchModel.pocket
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94GapPinchModel.merged_darts
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94GapPinchModel.gap_face_not_mem
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94GapPinchModel.not_leastArea
