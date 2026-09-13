import GroupApproximation.GGT.VanKampen.SurgeryCornerJoinMap
import GroupApproximation.GGT.VanKampen.SurgeryPinchSplitDiagram
import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import GroupApproximation.Meta.AxiomGuard

/-!
# Joining two vertices at corners of a G-face in a disc diagram

The inverse of `PinchSplit.Input.diagram`.  At two distinct vertices whose corners lie on one
G-face, join the vertices (`CornerJoin.toCombMap`), splitting the face into two G-faces.  Darts,
edge reversal and labels are unchanged, and every other face keeps its literal enumeration, so
the exterior boundary word and every relator cell survive letter for letter.

An `Input` is two darts at distinct vertices, the walk of their common face from the corner of
`x` cut at the corner of `y`, the face neither the exterior nor a relator face, and the value of
one of the two halves.

* `kept`: old faces to faces of the join, `kept (faceOf d) = faceOf d` for every dart off the
  joined face (`kept_faceOf`); every other face goes to a distinct face (`kept_inj`) other than
  the two new faces (`kept_ne_left`, `kept_ne_right`), and these are all the faces (`face_cases`).
* `diagram`: the joined disc diagram, with `faceBoundary_left_darts` (`alpha x :: ys`),
  `faceBoundary_right_darts` (`alpha y :: xs`), `faceBoundary_kept_darts` (the old walk of every
  other face), `left_ne_right`, `faceCount_eq`, `vertexCount_add_one`, `sameCycle_iff`.
* `boundaryWord_eq`, `cellMap`, `cellDarts_eq`, `outerDarts_eq`, `replacement`, `oEquivalent`,
  `rCellCount_eq`, `reduced`, `label_isLetter`.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.CornerJoin

open HullSC
open GroupApproximation.GGT.VanKampen.Embedded

universe u w v

/-- A trivial cyclic product with a trivial half, cut at two letters, has a trivial other half. -/
theorem prod_split_eq_one {H : Type u} [Group H] (a b : H) (xs ys : List H)
    (h : (a :: xs ++ b :: ys).prod = 1) (hY : (a :: ys).prod = 1) : (b :: xs).prod = 1 := by
  rw [List.prod_append, List.prod_cons, List.prod_cons] at h
  rw [List.prod_cons] at hY
  rw [List.prod_cons]
  have h' : b * ys.prod * (a * xs.prod) = 1 := mul_eq_one_comm.mp h
  have hY' : ys.prod * a = 1 := mul_eq_one_comm.mp hY
  calc b * xs.prod = b * (ys.prod * a) * xs.prod := by rw [hY', mul_one]
    _ = b * ys.prod * (a * xs.prod) := by simp only [mul_assoc]
    _ = 1 := h'

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **A corner join across a G-face**: two darts at distinct vertices whose corners lie on one
face, neither the exterior nor a relator face, with the walk of that face from the corner of `x`
cut at the corner of `y`, and the left half `alpha x :: ys` of trivial value. -/
structure Input (Delta : DiscDiagram.{u, w, v} W) where
  x : Delta.toCombMap.Dart
  y : Delta.toCombMap.Dart
  not_same_vertex : ¬ Delta.toCombMap.sigma.SameCycle x y
  xs : List Delta.toCombMap.Dart
  ys : List Delta.toCombMap.Dart
  cycle : Delta.toCombMap.IsFaceCycle
    (Delta.toCombMap.alpha x :: xs ++ Delta.toCombMap.alpha y :: ys)
  face_ne_outer : Delta.toCombMap.faceOf (Delta.toCombMap.alpha x) ≠ Delta.outerFace
  not_cell : ∀ C ∈ Delta.relatorCells,
    C.face ≠ Delta.toCombMap.faceOf (Delta.toCombMap.alpha x)
  left_value : RelLetter.listVal ((Delta.toCombMap.alpha x :: ys).map Delta.label) = 1

namespace Input

variable {Delta : DiscDiagram.{u, w, v} W} (I : Input Delta)

/-- The walk of the joined face, as map data. -/
abbrev cycles : Cycle Delta.toCombMap I.x I.y := ⟨I.xs, I.ys, I.cycle⟩

/-- The face through both corners. -/
abbrev face : Delta.toCombMap.Face := Delta.toCombMap.faceOf (Delta.toCombMap.alpha I.x)

theorem outer_ne_face : Delta.outerFace ≠ I.face := fun h => I.face_ne_outer h.symm

theorem faceOf_out_old (g : Delta.toCombMap.Face) : Delta.toCombMap.faceOf g.out = g :=
  Quotient.out_eq g

/-- The joined face is a G-face. -/
theorem face_value : RelLetter.listVal (Delta.faceWord I.face) = 1 := by
  rcases Delta.inner_face I.face I.face_ne_outer with ⟨C, hC, hface⟩ | h
  · exact absurd hface (I.not_cell C hC)
  · exact h

/-- The walk from the corner of `x` reads a trivial word. -/
theorem cycle_value : RelLetter.listVal ((Delta.toCombMap.alpha I.x :: I.xs ++
    Delta.toCombMap.alpha I.y :: I.ys).map Delta.label) = 1 := by
  obtain ⟨k, hk, hrot⟩ := (Delta.faceBoundary I.face).isFaceCycle.exists_rotate_eq
    I.cycle (FaceBoundary.faceOf_head _)
  rw [← hrot, List.map_rotate]
  exact PinchSplit.listVal_rotate_eq_one_of_eq_one k (by rw [List.length_map]; exact hk)
    I.face_value

/-- **The right half is trivial**, since the whole walk and the left half are. -/
theorem right_value :
    RelLetter.listVal ((Delta.toCombMap.alpha I.y :: I.xs).map Delta.label) = 1 := by
  have e : ∀ l : List Delta.toCombMap.Dart, RelLetter.listVal (l.map Delta.label) =
      (l.map fun d => (Delta.label d).val).prod := fun l => by
    change ((l.map Delta.label).map RelLetter.val).prod = _
    rw [List.map_map]
    rfl
  have hC := I.cycle_value
  have hL := I.left_value
  rw [e, List.map_append, List.map_cons, List.map_cons] at hC
  rw [e, List.map_cons] at hL
  rw [e, List.map_cons]
  exact prod_split_eq_one _ _ _ _ hC hL

variable [DecidableEq Delta.toCombMap.Dart]

/-- The left new face, of the corner after `x`. -/
abbrev leftFace : (toCombMap Delta.toCombMap I.x I.y).Face :=
  (toCombMap Delta.toCombMap I.x I.y).faceOf (Delta.toCombMap.alpha I.x)

/-- The right new face, of the corner after `y`. -/
abbrev rightFace : (toCombMap Delta.toCombMap I.x I.y).Face :=
  (toCombMap Delta.toCombMap I.x I.y).faceOf (Delta.toCombMap.alpha I.y)

/-- **The two new faces are distinct.** -/
theorem left_ne_right : I.leftFace ≠ I.rightFace :=
  I.cycles.left_ne_right

theorem faceOf_out_new (F : (toCombMap Delta.toCombMap I.x I.y).Face) :
    (toCombMap Delta.toCombMap I.x I.y).faceOf F.out = F :=
  Quotient.out_eq F

/-- **Old faces to faces of the join.**  Only the image of the joined face is not canonical. -/
noncomputable def kept (g : Delta.toCombMap.Face) : (toCombMap Delta.toCombMap I.x I.y).Face :=
  (toCombMap Delta.toCombMap I.x I.y).faceOf g.out

/-- A dart off the joined face lies on the image of its face. -/
theorem kept_faceOf (d : Delta.toCombMap.Dart) (hd : Delta.toCombMap.faceOf d ≠ I.face) :
    I.kept (Delta.toCombMap.faceOf d) = (toCombMap Delta.toCombMap I.x I.y).faceOf d :=
  (I.cycles.faceOf_eq_iff_of_ne hd _).mpr (faceOf_out_old _)

theorem kept_ne_left {g : Delta.toCombMap.Face} (hg : g ≠ I.face) : I.kept g ≠ I.leftFace :=
  fun h => hg ((faceOf_out_old g).symm.trans ((I.cycles.faceOf_old_iff g.out).mpr (Or.inl h)))

theorem kept_ne_right {g : Delta.toCombMap.Face} (hg : g ≠ I.face) : I.kept g ≠ I.rightFace :=
  fun h => hg ((faceOf_out_old g).symm.trans ((I.cycles.faceOf_old_iff g.out).mpr (Or.inr h)))

/-- **Faces off the joined face stay distinct.** -/
theorem kept_inj {g h : Delta.toCombMap.Face} (hg : g ≠ I.face) (heq : I.kept g = I.kept h) :
    g = h := by
  have hgo : Delta.toCombMap.faceOf g.out ≠ I.face := by
    rw [faceOf_out_old]
    exact hg
  have h' := (I.cycles.faceOf_eq_iff_of_ne hgo h.out).mp heq.symm
  rw [faceOf_out_old, faceOf_out_old] at h'
  exact h'.symm

/-- **Every face of the join is a new face or a kept face off the joined face.** -/
theorem face_cases (F : (toCombMap Delta.toCombMap I.x I.y).Face) :
    F = I.leftFace ∨ F = I.rightFace ∨ ∃ g, g ≠ I.face ∧ F = I.kept g := by
  obtain ⟨d, rfl⟩ := Quotient.exists_rep F
  by_cases h : Delta.toCombMap.faceOf d = I.face
  · rcases (I.cycles.faceOf_old_iff d).mp h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr ⟨Delta.toCombMap.faceOf d, h, (I.kept_faceOf d h).symm⟩)

/-- The image of a face other than the old exterior is not the image of the exterior. -/
theorem kept_ne_kept_outer {g : Delta.toCombMap.Face} (hg : g ≠ Delta.outerFace) :
    I.kept g ≠ I.kept Delta.outerFace := by
  intro heq
  by_cases h : g = I.face
  · rcases (I.cycles.faceOf_old_iff g.out).mp ((faceOf_out_old g).trans h) with h' | h'
    · exact I.kept_ne_left I.outer_ne_face (heq.symm.trans h')
    · exact I.kept_ne_right I.outer_ne_face (heq.symm.trans h')
  · exact hg (I.kept_inj h heq)

/-- A face off the joined face keeps its enumeration. -/
theorem keptCycle {g : Delta.toCombMap.Face} (hg : g ≠ I.face) :
    (toCombMap Delta.toCombMap I.x I.y).IsFaceCycle (Delta.faceBoundary g).darts :=
  I.cycles.isFaceCycle_of_ne (Delta.faceBoundary g).isFaceCycle
    (by rw [FaceBoundary.faceOf_head]; exact hg)

theorem out_ne_face {F : (toCombMap Delta.toCombMap I.x I.y).Face} (hL : F ≠ I.leftFace)
    (hR : F ≠ I.rightFace) : Delta.toCombMap.faceOf F.out ≠ I.face := fun h =>
  ((I.cycles.faceOf_old_iff F.out).mp h).elim (fun h' => hL ((I.faceOf_out_new F).symm.trans h'))
    (fun h' => hR ((I.faceOf_out_new F).symm.trans h'))

/-- A kept face is represented by a dart of the old face. -/
theorem faceOf_out_kept {g : Delta.toCombMap.Face} (hg : g ≠ I.face) :
    Delta.toCombMap.faceOf (I.kept g).out = g := by
  have hgo : Delta.toCombMap.faceOf g.out ≠ I.face := by
    rw [faceOf_out_old]
    exact hg
  exact ((I.cycles.faceOf_eq_iff_of_ne hgo _).mp (I.faceOf_out_new _)).trans (faceOf_out_old g)

open scoped Classical in
/-- The face boundaries of the join: the two halves at the new faces, the old walk at every other
face. -/
noncomputable def faceBoundary (F : (toCombMap Delta.toCombMap I.x I.y).Face) :
    FaceBoundary (toCombMap Delta.toCombMap I.x I.y) F :=
  if hL : F = I.leftFace then
    I.cycles.isFaceCycle_left.toFaceBoundary.congr hL.symm
  else if hR : F = I.rightFace then
    I.cycles.isFaceCycle_right.toFaceBoundary.congr hR.symm
  else
    (I.keptCycle (I.out_ne_face hL hR)).toFaceBoundary.congr
      (((I.cycles.faceOf_eq_iff_of_ne (I.out_ne_face hL hR) _).mpr
        (FaceBoundary.faceOf_head _)).trans (I.faceOf_out_new F))

/-- **The left new face reads `alpha x :: ys`.** -/
theorem faceBoundary_left_darts :
    (I.faceBoundary I.leftFace).darts = Delta.toCombMap.alpha I.x :: I.ys := by
  unfold faceBoundary
  rw [dif_pos rfl]
  rfl

/-- **The right new face reads `alpha y :: xs`.** -/
theorem faceBoundary_right_darts :
    (I.faceBoundary I.rightFace).darts = Delta.toCombMap.alpha I.y :: I.xs := by
  unfold faceBoundary
  rw [dif_neg I.left_ne_right.symm, dif_pos rfl]
  rfl

/-- **A face off the joined face reads its old walk.** -/
theorem faceBoundary_kept_darts (g : Delta.toCombMap.Face) (hg : g ≠ I.face) :
    (I.faceBoundary (I.kept g)).darts = (Delta.faceBoundary g).darts := by
  unfold faceBoundary
  rw [dif_neg (I.kept_ne_left hg), dif_neg (I.kept_ne_right hg)]
  change (Delta.faceBoundary (Delta.toCombMap.faceOf (I.kept g).out)).darts =
    (Delta.faceBoundary g).darts
  rw [I.faceOf_out_kept hg]

/-- A relator record of the old diagram on the image of its face. -/
noncomputable def cell (C : RelatorCell Delta.toCombMap Delta.outerFace W) :
    RelatorCell (toCombMap Delta.toCombMap I.x I.y) (I.kept Delta.outerFace) W where
  face := I.kept C.face
  face_ne_outer := I.kept_ne_kept_outer C.face_ne_outer
  word := C.word
  word_mem := C.word_mem
  conjugator := C.conjugator
  reversed := C.reversed

theorem left_faceWord_value :
    RelLetter.listVal ((I.faceBoundary I.leftFace).darts.map Delta.label) = 1 := by
  rw [I.faceBoundary_left_darts]
  exact I.left_value

theorem right_faceWord_value :
    RelLetter.listVal ((I.faceBoundary I.rightFace).darts.map Delta.label) = 1 := by
  rw [I.faceBoundary_right_darts]
  exact I.right_value

/-- **The joined disc diagram.** -/
noncomputable def diagram : DiscDiagram.{u, w, v} W where
  toCombMap := toCombMap Delta.toCombMap I.x I.y
  planar := I.cycles.planar Delta.planar I.not_same_vertex
  label := Delta.label
  label_alpha := Delta.label_alpha
  outerFace := I.kept Delta.outerFace
  faceBoundary := I.faceBoundary
  relatorCells := Delta.relatorCells.map I.cell
  relatorCell_faces_nodup := by
    have hmap : (Delta.relatorCells.map I.cell).map RelatorCell.face =
        (Delta.relatorCells.map RelatorCell.face).map I.kept := by
      rw [List.map_map, List.map_map]
      exact List.map_congr_left fun _ _ => rfl
    rw [hmap]
    refine List.Nodup.map_on ?_ Delta.relatorCell_faces_nodup
    intro f hf f' _ hff'
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hf
    exact I.kept_inj (I.not_cell C hC) hff'
  relatorCell_word := by
    intro C' hC'
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hC'
    change C.word = (I.faceBoundary (I.kept C.face)).darts.map Delta.label
    rw [I.faceBoundary_kept_darts C.face (I.not_cell C hC)]
    exact Delta.relatorCell_word C hC
  inner_face := by
    intro F hF
    rcases I.face_cases F with rfl | rfl | ⟨g, hg, rfl⟩
    · right
      exact I.left_faceWord_value
    · right
      exact I.right_faceWord_value
    · have hgo : g ≠ Delta.outerFace := fun h => hF (by rw [h])
      rcases Delta.inner_face g hgo with ⟨C, hC, hface⟩ | hone
      · left
        refine ⟨I.cell C, List.mem_map.mpr ⟨C, hC, rfl⟩, ?_⟩
        change I.kept C.face = I.kept g
        rw [hface]
      · right
        rw [I.faceBoundary_kept_darts g hg]
        exact hone
  boundary_product := by
    have hvalues : (Delta.relatorCells.map I.cell).map RelatorCell.value =
        Delta.relatorCells.map RelatorCell.value := by
      rw [List.map_map]
      exact List.map_congr_left fun _ _ => rfl
    rw [hvalues, Delta.boundary_product]
    change RelLetter.listVal (RelWord.revInv ((Delta.faceBoundary Delta.outerFace).darts.map
        Delta.label)) =
      RelLetter.listVal (RelWord.revInv ((I.faceBoundary (I.kept Delta.outerFace)).darts.map
        Delta.label))
    rw [I.faceBoundary_kept_darts Delta.outerFace I.outer_ne_face]

theorem diagram_toCombMap : I.diagram.toCombMap = toCombMap Delta.toCombMap I.x I.y := rfl

theorem diagram_outerFace : I.diagram.outerFace = I.kept Delta.outerFace := rfl

/-- A dart off the joined face lies on the image of its old face. -/
theorem diagram_faceOf (d : Delta.toCombMap.Dart) (hd : Delta.toCombMap.faceOf d ≠ I.face) :
    I.diagram.toCombMap.faceOf d = I.kept (Delta.toCombMap.faceOf d) :=
  (I.kept_faceOf d hd).symm

/-- **The exterior boundary word is unchanged.** -/
theorem boundaryWord_eq : I.diagram.boundaryWord = Delta.boundaryWord := by
  change RelWord.revInv ((I.faceBoundary (I.kept Delta.outerFace)).darts.map Delta.label) =
    RelWord.revInv ((Delta.faceBoundary Delta.outerFace).darts.map Delta.label)
  rw [I.faceBoundary_kept_darts Delta.outerFace I.outer_ne_face]

/-- **The ordered relator cells are the old ones**, on the images of their faces. -/
noncomputable def cellMap : Surgery.OrderedRCellMap Delta I.diagram I.kept where
  cell := I.cell
  face_eq _ := rfl
  word_eq _ := rfl
  conjugator_eq _ := rfl
  reversed_eq _ := rfl
  list_eq := rfl

/-- The join is a G-region replacement. -/
noncomputable def replacement : Surgery.OrderedGRegionReplacement.{u, w, v, v} Delta :=
  ⟨I.diagram, I.boundaryWord_eq, I.cellMap.orderedTransport⟩

/-- **The join is O-equivalent to the old diagram.** -/
noncomputable def oEquivalent : OEquivalentDiscDiagram Delta I.diagram :=
  I.replacement.oEquivalent

/-- The join keeps the number of relator cells. -/
theorem rCellCount_eq : I.diagram.rCellCount = Delta.rCellCount :=
  I.cellMap.orderedTransport.rCellCount_eq

/-- **Reducedness survives the join.** -/
theorem reduced (hred : Delta.Reduced) : I.diagram.Reduced :=
  I.cellMap.orderedTransport.reduced hred

/-- Labels are unchanged, so legality is kept. -/
theorem label_isLetter (E : RelGenSet G Lambda) (h : ∀ d, E.IsLetter (Delta.label d))
    (d : I.diagram.toCombMap.Dart) : E.IsLetter (I.diagram.label d) :=
  h d

/-- **Every relator cell keeps its walk**, along the cell index map. -/
theorem cellDarts_eq (i : Fin Delta.rCellCount) :
    cellDarts I.diagram (I.cellMap.indexEquiv i) = (cellDarts Delta i).map id := by
  rw [List.map_id]
  change (I.diagram.faceBoundary (Embedded.cell I.diagram (I.cellMap.indexEquiv i)).face).darts =
    (Delta.faceBoundary (Embedded.cell Delta i).face).darts
  rw [I.cellMap.indexed_cell i]
  change (I.faceBoundary (I.kept (Embedded.cell Delta i).face)).darts = _
  rw [I.faceBoundary_kept_darts _ (I.not_cell _ (Embedded.cell_mem Delta i))]

/-- **The exterior keeps its walk.** -/
theorem outerDarts_eq : outerDarts I.diagram = (outerDarts Delta).map id := by
  rw [List.map_id]
  change (I.faceBoundary (I.kept Delta.outerFace)).darts.reverse.map Delta.toCombMap.alpha =
    (Delta.faceBoundary Delta.outerFace).darts.reverse.map Delta.toCombMap.alpha
  rw [I.faceBoundary_kept_darts _ I.outer_ne_face]

/-- The left new face is not the exterior. -/
theorem left_ne_outer : I.leftFace ≠ I.diagram.outerFace :=
  fun h => I.kept_ne_left I.outer_ne_face h.symm

/-- The right new face is not the exterior. -/
theorem right_ne_outer : I.rightFace ≠ I.diagram.outerFace :=
  fun h => I.kept_ne_right I.outer_ne_face h.symm

/-- No relator cell of the join sits on the left new face. -/
theorem left_not_cell : ∀ C ∈ I.diagram.relatorCells, C.face ≠ I.leftFace := by
  intro C hC
  obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
  exact I.kept_ne_left (I.not_cell C₀ hC₀)

/-- No relator cell of the join sits on the right new face. -/
theorem right_not_cell : ∀ C ∈ I.diagram.relatorCells, C.face ≠ I.rightFace := by
  intro C hC
  obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
  exact I.kept_ne_right (I.not_cell C₀ hC₀)

/-- A face off the joined face reads its old word. -/
theorem faceWord_kept (g : Delta.toCombMap.Face) (hg : g ≠ I.face) :
    I.diagram.faceWord (I.kept g) = Delta.faceWord g :=
  congrArg (fun l => l.map Delta.label) (I.faceBoundary_kept_darts g hg)

/-- **One face more.** -/
theorem faceCount_eq : I.diagram.toCombMap.faceCount = Delta.toCombMap.faceCount + 1 :=
  I.cycles.faceCount_eq

/-- **One vertex fewer.** -/
theorem vertexCount_add_one :
    I.diagram.toCombMap.vertexCount + 1 = Delta.toCombMap.vertexCount :=
  CornerJoin.vertexCount_add_one Delta.toCombMap I.x I.y I.not_same_vertex

/-- **The vertices of the join**: the old vertices, with the vertices of `x` and `y` made one. -/
theorem sameCycle_iff (z z' : Delta.toCombMap.Dart) :
    I.diagram.toCombMap.sigma.SameCycle z z' ↔ Delta.toCombMap.sigma.SameCycle z z' ∨
      ((Delta.toCombMap.sigma.SameCycle I.x z ∨ Delta.toCombMap.sigma.SameCycle I.y z) ∧
        (Delta.toCombMap.sigma.SameCycle I.x z' ∨ Delta.toCombMap.sigma.SameCycle I.y z')) :=
  sigma_sameCycle_iff Delta.toCombMap I.x I.y I.not_same_vertex z z'

end Input

end GroupApproximation.GGT.VanKampen.CornerJoin

#audit_axioms GroupApproximation.GGT.VanKampen.CornerJoin.prod_split_eq_one
#audit_axioms GroupApproximation.GGT.VanKampen.CornerJoin.Input.right_value
#audit_axioms GroupApproximation.GGT.VanKampen.CornerJoin.Input.diagram
#audit_axioms GroupApproximation.GGT.VanKampen.CornerJoin.Input.boundaryWord_eq
#audit_axioms GroupApproximation.GGT.VanKampen.CornerJoin.Input.cellMap
#audit_axioms GroupApproximation.GGT.VanKampen.CornerJoin.Input.oEquivalent
#audit_axioms GroupApproximation.GGT.VanKampen.CornerJoin.Input.reduced
#audit_axioms GroupApproximation.GGT.VanKampen.CornerJoin.Input.face_cases
#audit_axioms GroupApproximation.GGT.VanKampen.CornerJoin.Input.kept_inj
#audit_axioms GroupApproximation.GGT.VanKampen.CornerJoin.Input.faceBoundary_left_darts
#audit_axioms GroupApproximation.GGT.VanKampen.CornerJoin.Input.faceBoundary_right_darts
#audit_axioms GroupApproximation.GGT.VanKampen.CornerJoin.Input.faceBoundary_kept_darts
#audit_axioms GroupApproximation.GGT.VanKampen.CornerJoin.Input.cellDarts_eq
#audit_axioms GroupApproximation.GGT.VanKampen.CornerJoin.Input.outerDarts_eq
#audit_axioms GroupApproximation.GGT.VanKampen.CornerJoin.Input.faceCount_eq
#audit_axioms GroupApproximation.GGT.VanKampen.CornerJoin.Input.vertexCount_add_one
#audit_axioms GroupApproximation.GGT.VanKampen.CornerJoin.Input.sameCycle_iff
