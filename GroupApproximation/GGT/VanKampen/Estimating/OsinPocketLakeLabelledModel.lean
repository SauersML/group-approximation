import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLakeModel
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLakeAbsorption
import GroupApproximation.GGT.VanKampen.SurgeryPinchSplitDiagram
import GroupApproximation.Meta.AxiomGuard

/-!
# The labelled lake: a two-petal rose with two relator cells

A model test for the open case of `PocketPinchLabelledStatement` (`Estimating/OsinPocketPieces.lean`),
a lake that contains the source cell `Π`.

The map is the rose of `Estimating/OsinPocketLakeModel.lean`. It has four darts, the edges `{0,1}`
and `{2,3}`, one vertex with rotation `0 ↦ 1 ↦ 2 ↦ 3 ↦ 0`, and three faces `K = [0,2]`, `Π = [1]`
and `O = [3]`. Here `Π` reads `x` and `K` reads `x⁻¹ y⁻¹`. Both are relator cells, and `O` is the
exterior face, reading `y` (`roseDiagram`).

* `pinchedK`: the face set `{K}` is a pocket face set between the positions `0` and `1`. Its source
  is `Π` and its kept cell is `K`. It has empty sides, the arc `[1]` of `Π` read backwards and the
  arc `[2]` of the exterior. The labels are letters (`label_isLetter`), its cycle `[0,2]` is a closed
  walk (`pinchedK_closedWalk`), and it is not simple (`pinchedK_not_simple`). So it satisfies the
  hypotheses of `PocketPinchLabelledStatement`.
* `petalK`: the face set `{Π}` is a simple pocket face set of the same diagram (`petalK_simple`),
  between the same positions. The roles are swapped: its source is `K` and its kept cell is `Π`. It
  has the arc `[0]` of `K` read backwards and an empty arc of the exterior. So the conclusion of
  `PocketPinchLabelledStatement` at `pinchedK` holds (`pinchedPocketPetal_conclusion`).
* The vertex split does not apply. The walk passes twice through the one vertex, and the corners
  there off `{K}` lie on `Π`, a relator cell (`corner_zero`), and on the exterior face
  (`corner_two`); these are all of them (`not_mem_faces_corner_iff`). No face of the rose is a
  `G`-face, so `PinchSplit.Input` is empty (`isEmpty_input`).
* Lake absorption does not apply. Every dart lies on an edge of the boundary of `{K}`
  (`boundaryEdge`). So the exterior piece is `{O}` (`eq_outer_of_mem_component`). The source cell
  `Π` does not face it (`source_not_mem_component`), against the hypothesis of
  `PocketFaceSet.absorb`, and filling the lakes takes `Π` in (`source_mem_absorbed`).

The endpoint `LakeRoseLabelledModel` records all of this. The model proves no case of the statement
beyond this instance.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.OsinPocketLakeLabelledModel

open Equiv GroupApproximation.HullSC GroupApproximation.WordMetric
open OsinPocketLakeModel (M faceClass faceRep faceEquiv vertexEquiv planar)
open OsinPocketPinchedTwoGonModel (G gx gy D)
open Surgery.MapCollapse (IsBoundaryDart BoundaryCycle)
open Surgery.MapCollapse.ExteriorComponent (BoundaryEdge component mem_component_iff
  absorbed mem_absorbed_iff)

def face (i : Fin 3) : M.Face := M.faceOf (faceRep i)

theorem faceEquiv_face (i : Fin 3) : faceEquiv (face i) = i := by
  change faceClass (faceRep i) = i
  fin_cases i <;> rfl

theorem faceOf_eq_face (d : Fin 4) (i : Fin 3) :
    M.faceOf d = face i ↔ faceClass d = i := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face]
  rfl

theorem face_eq_iff (i j : Fin 3) : face i = face j ↔ i = j := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face, faceEquiv_face]

/-- The rose has one vertex. -/
theorem vertex_eq (a b : M.Vertex) : a = b :=
  vertexEquiv.injective (Subsingleton.elim _ _)

def faceDarts : Fin 3 → List (Fin 4) := ![[0, 2], [1], [3]]

noncomputable def indexedBoundary (i : Fin 3) : FaceBoundary M (face i) where
  darts := faceDarts i
  nonempty := by change faceDarts i ≠ ([] : List (Fin 4)); fin_cases i <;> decide
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

theorem boundary_face_darts (i : Fin 3) :
    (boundary (face i)).darts = faceDarts i := by
  have htransport {f g : M.Face} (h : f = g) (B : FaceBoundary M f) :
      (h ▸ B).darts = B.darts := by cases h; rfl
  unfold boundary
  rw [htransport]
  exact congrArg faceDarts (faceEquiv_face i)

/-! ## The labelled rose -/

/-- The dart `1` of `Π` reads `x`, the dart `3` of the exterior reads `y`, and their reversals read
the inverses. -/
def label (d : Fin 4) : RelLetter G Empty :=
  .base ((![gx⁻¹, gx, gy⁻¹, gy] : Fin 4 → G) d)

def petalWord : List (RelLetter G Empty) := [.base gx]
def pocketWord : List (RelLetter G Empty) := [.base gx⁻¹, .base gy⁻¹]

/-- The relators `x` and `x⁻¹ y⁻¹`. -/
def W : Set (List (RelLetter G Empty)) := {petalWord, pocketWord}

def petalCell : RelatorCell M (face 2) W where
  face := face 1
  face_ne_outer := (face_eq_iff 1 2).not.mpr (by decide)
  word := petalWord
  word_mem := Set.mem_insert _ _
  conjugator := 1
  reversed := false

def pocketCell : RelatorCell M (face 2) W where
  face := face 0
  face_ne_outer := (face_eq_iff 0 2).not.mpr (by decide)
  word := pocketWord
  word_mem := Set.mem_insert_of_mem _ rfl
  conjugator := 1
  reversed := false

/-- **The rose with two relator cells**, `Π` and `K`. -/
noncomputable def roseDiagram : DiscDiagram W where
  toCombMap := M
  planar := planar
  label := label
  label_alpha := by
    intro d
    fin_cases d <;> exact congrArg RelLetter.base (by decide)
  outerFace := face 2
  faceBoundary := boundary
  relatorCells := [petalCell, pocketCell]
  relatorCell_faces_nodup := by
    change [face 1, face 0].Nodup
    exact List.nodup_cons.mpr ⟨fun h => absurd ((face_eq_iff 1 0).mp (List.mem_singleton.mp h))
      (by decide), List.nodup_singleton _⟩
  relatorCell_word := by
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · change petalWord = (boundary (face 1)).darts.map label
      rw [boundary_face_darts]
      rfl
    · rcases List.mem_singleton.mp hC with rfl
      change pocketWord = (boundary (face 0)).darts.map label
      rw [boundary_face_darts]
      rfl
  inner_face := by
    intro f hf
    obtain ⟨i, rfl⟩ : ∃ i, face i = f := ⟨faceEquiv f, faceEquiv.left_inv f⟩
    fin_cases i
    · exact Or.inl ⟨pocketCell, List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl)), rfl⟩
    · exact Or.inl ⟨petalCell, List.mem_cons.mpr (Or.inl rfl), rfl⟩
    · exact (hf rfl).elim
  boundary_product := by
    rw [boundary_face_darts]
    decide

instance roseDiagram_ofNat (n : ℕ) : OfNat roseDiagram.toCombMap.Dart n :=
  inferInstanceAs (OfNat (Fin 4) n)
instance roseDiagram_decidableEq : DecidableEq roseDiagram.toCombMap.Dart :=
  inferInstanceAs (DecidableEq (Fin 4))

/-- The index of `Π` in the stored cell order. -/
noncomputable def petalIndex : Fin roseDiagram.rCellCount := ⟨0, by decide⟩

/-- The index of `K` in the stored cell order. -/
noncomputable def pocketIndex : Fin roseDiagram.rCellCount := ⟨1, by decide⟩

/-- **The labels are letters** of the symmetrized alphabet. -/
theorem label_isLetter (d : roseDiagram.toCombMap.Dart) :
    (symmetricLabelAlphabet D).IsLetter (roseDiagram.label d) :=
  Or.inl (Set.mem_univ _)

theorem roseDiagram_cellDarts_petal : Embedded.cellDarts roseDiagram petalIndex = [1] := by
  change (boundary (face 1)).darts = _
  rw [boundary_face_darts]
  rfl

theorem roseDiagram_cellDarts_pocket : Embedded.cellDarts roseDiagram pocketIndex = [0, 2] := by
  change (boundary (face 0)).darts = _
  rw [boundary_face_darts]
  rfl

theorem roseDiagram_outerDarts : Embedded.outerDarts roseDiagram = [2] := by
  change ((boundary (face 2)).darts.reverse.map M.alpha) = _
  rw [boundary_face_darts]
  rfl

theorem empty_side_norm :
    WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal
      (Embedded.dartWord roseDiagram ([] : List roseDiagram.toCombMap.Dart))) ≤ 0 :=
  Nat.le_of_eq (WordMetric.wordNorm_one _)

/-! ## The pinched pocket `{K}` -/

/-- The face set `{K}`. -/
def pocketFaces : Finset roseDiagram.toCombMap.Face := {face 0}

theorem face_mem_pocketFaces_iff (i : Fin 3) : face i ∈ pocketFaces ↔ i = 0 :=
  Finset.mem_singleton.trans (face_eq_iff i 0)

theorem pocketBoundaryDart_iff (d : Fin 4) :
    IsBoundaryDart roseDiagram.toCombMap pocketFaces d ↔ d ∈ ([0, 2] : List (Fin 4)) := by
  change (M.faceOf d ∈ ({face 0} : Finset M.Face) ∧
    M.faceOf (M.alpha d) ∉ ({face 0} : Finset M.Face)) ↔ _
  simp only [Finset.mem_singleton, faceOf_eq_face]
  fin_cases d <;> decide

/-- The two boundary darts of `{K}`. -/
def pocketCycle : BoundaryCycle roseDiagram.toCombMap pocketFaces where
  cycle := ([0, 2] : List (Fin 4))
  cycle_nonempty := List.cons_ne_nil _ _
  cycle_nodup := (by decide : ([0, 2] : List (Fin 4)).Nodup)
  cycle_mem_iff := fun d => (pocketBoundaryDart_iff d).symm

/-- The arc `[1]` of `Π`. -/
def petalArc : Embedded.CyclicArc (Embedded.cellDarts roseDiagram petalIndex) where
  start := ⟨0, Nat.succ_pos _⟩
  length := 1
  length_le := by
    rw [roseDiagram_cellDarts_petal]
    decide

theorem petalArc_darts : petalArc.darts = [1] := by
  change ((Embedded.cellDarts roseDiagram petalIndex).drop 0 ++
    (Embedded.cellDarts roseDiagram petalIndex).take 0).take 1 = _
  rw [roseDiagram_cellDarts_petal]
  rfl

/-- The arc `[2]` of the exterior boundary. -/
def exteriorArc : Embedded.CyclicArc (Embedded.outerDarts roseDiagram) where
  start := ⟨0, Nat.succ_pos _⟩
  length := 1
  length_le := by
    rw [roseDiagram_outerDarts]
    decide

theorem exteriorArc_darts : exteriorArc.darts = [2] := by
  change ((Embedded.outerDarts roseDiagram).drop 0 ++
    (Embedded.outerDarts roseDiagram).take 0).take 1 = _
  rw [roseDiagram_outerDarts]
  rfl

/-- The cycle of `{K}` is the reversed arc `[1]` of `Π` and the arc `[2]` of the exterior, with
empty sides. -/
theorem pocket_decomposition :
    (pocketCycle : BoundaryCycle roseDiagram.toCombMap pocketFaces).cycle =
      [] ++ Embedded.invDarts roseDiagram petalArc.darts ++ [] ++ exteriorArc.darts := by
  rw [petalArc_darts, exteriorArc_darts]
  decide

/-- **The pinched pocket** `{K}`, with source `Π` and kept cell `K`. -/
noncomputable def pinchedK : PocketFaceSet D 0 roseDiagram 0 1 where
  faces := pocketFaces
  outerFace_not_mem := fun h => absurd ((face_mem_pocketFaces_iff 2).mp h) (by decide)
  source := petalIndex
  source_not_mem := fun h => absurd ((face_mem_pocketFaces_iff 1).mp h) (by decide)
  kept := pocketIndex
  kept_mem := (face_mem_pocketFaces_iff 0).mpr rfl
  sourceArc := petalArc
  targetArc := exteriorArc
  firstSide := []
  secondSide := []
  boundary := pocketCycle
  decomposition := pocket_decomposition
  firstSide_length_le := Nat.le_refl 0
  secondSide_length_le := Nat.le_refl 0
  firstSide_norm_le := empty_side_norm
  secondSide_norm_le := empty_side_norm
  lo_le := Nat.zero_le _
  le_hi := by decide

/-- The cycle `[0,2]` of the pinched pocket is a closed walk: the rose has one vertex. -/
theorem pinchedK_closedWalk : pinchedK.ClosedWalk :=
  And.intro (List.isChain_pair.mpr (vertex_eq _ _)) (vertex_eq _ _)

/-- The pinched pocket is not simple: both darts of its cycle start at the one vertex. -/
theorem pinchedK_not_simple : ¬ pinchedK.Simple :=
  OsinPocketLakeModel.lakeCycle_not_isSimpleClosedWalk

/-! ## The petal `{Π}` -/

/-- The face set `{Π}`. -/
def petalFaces : Finset roseDiagram.toCombMap.Face := {face 1}

theorem face_mem_petalFaces_iff (i : Fin 3) : face i ∈ petalFaces ↔ i = 1 :=
  Finset.mem_singleton.trans (face_eq_iff i 1)

theorem petalBoundaryDart_iff (d : Fin 4) :
    IsBoundaryDart roseDiagram.toCombMap petalFaces d ↔ d ∈ ([1] : List (Fin 4)) := by
  change (M.faceOf d ∈ ({face 1} : Finset M.Face) ∧
    M.faceOf (M.alpha d) ∉ ({face 1} : Finset M.Face)) ↔ _
  simp only [Finset.mem_singleton, faceOf_eq_face]
  fin_cases d <;> decide

/-- The one boundary dart of `{Π}`. -/
def petalCycle : BoundaryCycle roseDiagram.toCombMap petalFaces where
  cycle := ([1] : List (Fin 4))
  cycle_nonempty := List.cons_ne_nil _ _
  cycle_nodup := List.nodup_singleton _
  cycle_mem_iff := fun d => (petalBoundaryDart_iff d).symm

/-- The arc `[0]` of `K`. -/
def pocketArc : Embedded.CyclicArc (Embedded.cellDarts roseDiagram pocketIndex) where
  start := ⟨0, Nat.succ_pos _⟩
  length := 1
  length_le := by
    rw [roseDiagram_cellDarts_pocket]
    decide

theorem pocketArc_darts : pocketArc.darts = [0] := by
  change ((Embedded.cellDarts roseDiagram pocketIndex).drop 0 ++
    (Embedded.cellDarts roseDiagram pocketIndex).take 0).take 1 = _
  rw [roseDiagram_cellDarts_pocket]
  rfl

/-- The empty arc of the exterior boundary at the position `0`. -/
def emptyArc : Embedded.CyclicArc (Embedded.outerDarts roseDiagram) where
  start := ⟨0, Nat.succ_pos _⟩
  length := 0
  length_le := Nat.zero_le _

theorem emptyArc_darts : emptyArc.darts = [] := by
  change ((Embedded.outerDarts roseDiagram).drop 0 ++
    (Embedded.outerDarts roseDiagram).take 0).take 0 = _
  rfl

/-- The cycle of `{Π}` is the reversed arc `[0]` of `K`, with empty sides and an empty arc of the
exterior. -/
theorem petal_decomposition :
    (petalCycle : BoundaryCycle roseDiagram.toCombMap petalFaces).cycle =
      [] ++ Embedded.invDarts roseDiagram pocketArc.darts ++ [] ++ emptyArc.darts := by
  rw [pocketArc_darts, emptyArc_darts]
  decide

/-- **The petal** `{Π}`, with source `K` and kept cell `Π`. -/
noncomputable def petalK : PocketFaceSet D 0 roseDiagram 0 1 where
  faces := petalFaces
  outerFace_not_mem := fun h => absurd ((face_mem_petalFaces_iff 2).mp h) (by decide)
  source := pocketIndex
  source_not_mem := fun h => absurd ((face_mem_petalFaces_iff 0).mp h) (by decide)
  kept := petalIndex
  kept_mem := (face_mem_petalFaces_iff 1).mpr rfl
  sourceArc := pocketArc
  targetArc := emptyArc
  firstSide := []
  secondSide := []
  boundary := petalCycle
  decomposition := petal_decomposition
  firstSide_length_le := Nat.le_refl 0
  secondSide_length_le := Nat.le_refl 0
  firstSide_norm_le := empty_side_norm
  secondSide_norm_le := empty_side_norm
  lo_le := Nat.zero_le _
  le_hi := by decide

/-- **The cycle `[1]` of the petal is a simple closed walk.** -/
theorem petalCycle_isSimpleClosedWalk :
    IsSimpleClosedWalk roseDiagram.toCombMap ([1] : List (Fin 4)) where
  ne_nil := List.cons_ne_nil _ _
  chain := List.isChain_singleton _
  closes := vertex_eq _ _
  vertex_nodup := List.nodup_singleton _
  alpha_not_mem := by decide

/-- The petal is simple. -/
theorem petalK_simple : petalK.Simple :=
  petalCycle_isSimpleClosedWalk

/-- The petal is not a face subset of the pinched pocket. -/
theorem petalFaces_not_subset : ¬ petalFaces ⊆ pocketFaces := fun h =>
  absurd ((face_mem_pocketFaces_iff 1).mp (h ((face_mem_petalFaces_iff 1).mpr rfl))) (by decide)

/-- **The conclusion of `PocketPinchLabelledStatement` at `pinchedK`**, with the diagram itself as
the O-equivalent copy and the petal as the simple pocket face set. -/
theorem pinchedPocketPetal_conclusion :
    ∃ (X' : DiscDiagram.{0, 0, 0} W) (K' : PocketFaceSet D 0 X' 0 1),
      Nonempty (OEquivalentDiscDiagram roseDiagram X') ∧ K'.Simple :=
  ⟨roseDiagram, petalK, ⟨OEquivalentDiscDiagram.refl roseDiagram⟩, petalK_simple⟩

/-! ## Neither producer applies at `pinchedK` -/

/-- The corner after the dart `0` lies on `Π`, a relator cell. -/
theorem corner_zero :
    roseDiagram.toCombMap.faceOf (roseDiagram.toCombMap.alpha 0) =
      (Embedded.cell roseDiagram petalIndex).face :=
  (faceOf_eq_face _ 1).mpr (by decide)

/-- The corner after the dart `2` lies on the exterior face. -/
theorem corner_two :
    roseDiagram.toCombMap.faceOf (roseDiagram.toCombMap.alpha 2) = roseDiagram.outerFace :=
  (faceOf_eq_face _ 2).mpr (by decide)

/-- The corners off `{K}` at the vertex are the corners after `0` and `2`. -/
theorem not_mem_faces_corner_iff (x : Fin 4) :
    roseDiagram.toCombMap.faceOf (roseDiagram.toCombMap.alpha x) ∉ pinchedK.faces ↔
      x = 0 ∨ x = 2 := by
  change ¬ M.faceOf (M.alpha x) ∈ ({face 0} : Finset M.Face) ↔ _
  simp only [Finset.mem_singleton, faceOf_eq_face]
  fin_cases x <;> decide

/-- **No vertex split applies.** Every face of the rose is the exterior face or a relator cell, so
the diagram has no `PinchSplit.Input`. -/
theorem isEmpty_input : IsEmpty (PinchSplit.Input roseDiagram) := by
  refine ⟨fun I => ?_⟩
  obtain ⟨i, hi⟩ :
      ∃ i, face i = roseDiagram.toCombMap.faceOf (roseDiagram.toCombMap.alpha I.x) :=
    ⟨faceEquiv _, faceEquiv.left_inv _⟩
  fin_cases i
  · exact I.left_not_cell pocketCell (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl))) hi
  · exact I.left_not_cell petalCell (List.mem_cons.mpr (Or.inl rfl)) hi
  · exact I.left_ne_outer hi.symm

/-- Every dart of the rose lies on an edge of the boundary of `{K}`. -/
theorem boundaryEdge (x : Fin 4) : BoundaryEdge roseDiagram.toCombMap pocketFaces x := by
  change (M.faceOf x ∈ ({face 0} : Finset M.Face) ∧
      M.faceOf (M.alpha x) ∉ ({face 0} : Finset M.Face)) ∨
    (M.faceOf (M.alpha x) ∈ ({face 0} : Finset M.Face) ∧
      M.faceOf (M.alpha (M.alpha x)) ∉ ({face 0} : Finset M.Face))
  simp only [Finset.mem_singleton, faceOf_eq_face]
  fin_cases x <;> decide

/-- **The exterior piece of `{K}` is the exterior face alone.** -/
theorem eq_outer_of_mem_component {f : roseDiagram.toCombMap.Face}
    (hf : f ∈ component roseDiagram.toCombMap pocketFaces roseDiagram.outerFace) :
    f = roseDiagram.outerFace := by
  obtain ⟨y, rfl, x, hx, hxy⟩ := mem_component_iff.mp hf
  rw [← hx]
  exact ((roseDiagram.toCombMap.faceOf_eq_iff x y).mpr
    (CombMap.facePerm_sameCycle_of_faceClass _ hxy boundaryEdge)).symm

/-- **The source cell `Π` does not face the exterior piece**, so `PocketFaceSet.absorb` does not
apply to `pinchedK`. -/
theorem source_not_mem_component :
    (Embedded.cell roseDiagram pinchedK.source).face ∉
      component roseDiagram.toCombMap pinchedK.faces roseDiagram.outerFace := fun h =>
  absurd ((face_eq_iff 1 2).mp (eq_outer_of_mem_component h)) (by decide)

/-- Filling the lakes of `{K}` takes in `Π`. -/
theorem source_mem_absorbed :
    (Embedded.cell roseDiagram pinchedK.source).face ∈
      absorbed roseDiagram.toCombMap pinchedK.faces roseDiagram.outerFace :=
  mem_absorbed_iff.mpr source_not_mem_component

/-- **The labelled lake** (model test). There is a disc diagram with letters for labels and a
pocket face set whose cycle is a closed walk and is not simple. The diagram has no vertex split
input, and the source cell does not face the exterior piece. Between the same positions the
diagram has a simple pocket face set that is not a face subset of the first, with the source and
kept cells swapped. -/
def LakeRoseLabelledModel : Prop :=
  ∃ (X : DiscDiagram.{0, 0, 0} W) (K : PocketFaceSet D 0 X 0 1),
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) ∧ K.ClosedWalk ∧ ¬ K.Simple ∧
      IsEmpty (PinchSplit.Input X) ∧
      (Embedded.cell X K.source).face ∉ component X.toCombMap K.faces X.outerFace ∧
      ∃ K' : PocketFaceSet D 0 X 0 1,
        ¬ K'.faces ⊆ K.faces ∧ K'.source = K.kept ∧ K'.kept = K.source ∧ K'.Simple

theorem lakeRoseLabelledModel : LakeRoseLabelledModel :=
  ⟨roseDiagram, pinchedK, label_isLetter, pinchedK_closedWalk, pinchedK_not_simple, isEmpty_input,
    source_not_mem_component, petalK, petalFaces_not_subset, rfl, rfl, petalK_simple⟩

#audit_axioms roseDiagram
#audit_axioms label_isLetter
#audit_axioms pinchedK
#audit_closed_axioms pinchedK_closedWalk
#audit_axioms pinchedK_not_simple
#audit_axioms petalK
#audit_closed_axioms petalK_simple
#audit_closed_axioms pinchedPocketPetal_conclusion
#audit_closed_axioms isEmpty_input
#audit_axioms source_not_mem_component
#audit_axioms source_mem_absorbed
#audit_closed_axioms lakeRoseLabelledModel

end GroupApproximation.GGT.VanKampen.OsinPocketLakeLabelledModel
