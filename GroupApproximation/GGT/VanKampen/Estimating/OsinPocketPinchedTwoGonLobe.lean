import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchedTwoGonRegion
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchUnpinched
import GroupApproximation.Meta.AxiomGuard

/-!
# A lobe of the pinched two-gon pocket

A model test for `PocketPinchPinchedStatement` (`Estimating/OsinPocketPinchUnpinched.lean`), the
pinched case of `PocketPinchStatement` (`Estimating/OsinPocketPieces.lean`): a pocket face set
`Γ_1` with `∂Γ_1 = s_1 t_1 s_2 t_2` has an O-equivalent copy with a simple pocket face set in the
same positions.

The map is the ten-dart map of `Estimating/OsinPocketPinchedTwoGonModel.lean`: a relator cell
`Π = [0,1,2]`, two digons `a = [3,4]` and `b = [5,6]` meeting only at the vertex `{1,3,6,8}`, and
the exterior face `[7,9,8]`.  Here the digon `a`, which reads `x⁻¹ x`, is a second relator cell
(`lobeDiagram`, with the relators `x y z` and `x⁻¹ x`).

* `pinchedK`: the face set `{a, b}` is a pocket face set with source `Π`, kept cell `a`, empty
  sides, the arc `[0,1]` of `Π` read backwards and the arc `[4,6]` of the exterior, between the
  positions `0` and `2`.  Its cycle `[5,3,4,6]` does not follow the boundary
  (`pinchedK_not_followsBoundary`), the darts `3` and `6` start at one vertex
  (`pinchedK_not_unpinched`), and it is not simple (`pinchedK_not_simple`).  So it satisfies the
  hypothesis of `PocketPinchPinchedStatement`.
* `lobeK`: the face set `{a}` is a simple pocket face set of the same diagram (`lobeK_simple`), with
  the same source and kept cells, the arc `[0]` of `Π` read backwards and the arc `[4]` of the
  exterior, between the same positions.

So the conclusion of `PocketPinchPinchedStatement` at `pinchedK` holds with the diagram itself as
the O-equivalent copy (`pinchedPocketLobe_conclusion`).  The statement ties the simple pocket face
set to `D`, `ε`, `lo` and `hi` only, and a lobe of a pinched pocket can serve
(`pinchedPocketLobeModel`).  The model proves no case of the statement beyond this instance.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 1636,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.OsinPocketPinchedTwoGonModel

open Surgery.MapCollapse (IsBoundaryDart BoundaryCycle Unpinched)

/-! ## The digon `a` as a relator cell -/

/-- The word `x⁻¹ x` of the digon `a`. -/
def digonWord : List (RelLetter G Empty) := [.base gx⁻¹, .base gx]

/-- The relators `x y z` and `x⁻¹ x`. -/
def lobeW : Set (List (RelLetter G Empty)) := {relator, digonWord}

def lobeRelatorCell : RelatorCell M (face 3) lobeW where
  face := face 0
  face_ne_outer := (face_eq_iff 0 3).not.mpr (by decide)
  word := relator
  word_mem := Set.mem_insert _ _
  conjugator := 1
  reversed := false

def digonCell : RelatorCell M (face 3) lobeW where
  face := face 1
  face_ne_outer := (face_eq_iff 1 3).not.mpr (by decide)
  word := digonWord
  word_mem := Set.mem_insert_of_mem _ rfl
  conjugator := 1
  reversed := false

/-- **The model map with two relator cells**, `Π` and the digon `a`. -/
noncomputable def lobeDiagram : DiscDiagram lobeW where
  toCombMap := M
  planar := planar
  label := label
  label_alpha := by
    intro d
    fin_cases d <;> exact congrArg RelLetter.base (by decide)
  outerFace := face 3
  faceBoundary := boundary
  relatorCells := [lobeRelatorCell, digonCell]
  relatorCell_faces_nodup := by
    change [face 0, face 1].Nodup
    exact List.nodup_cons.mpr ⟨fun h => absurd ((face_eq_iff 0 1).mp (List.mem_singleton.mp h))
      (by decide), List.nodup_singleton _⟩
  relatorCell_word := by
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · change relator = (boundary (face 0)).darts.map label
      rw [boundary_face_darts]
      rfl
    · rcases List.mem_singleton.mp hC with rfl
      change digonWord = (boundary (face 1)).darts.map label
      rw [boundary_face_darts]
      rfl
  inner_face := by
    intro f hf
    obtain ⟨i, rfl⟩ : ∃ i, face i = f := ⟨faceEquiv f, faceEquiv.left_inv f⟩
    fin_cases i
    · exact Or.inl ⟨lobeRelatorCell, List.mem_cons.mpr (Or.inl rfl), rfl⟩
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

instance lobeDiagram_neZero : NeZero lobeDiagram.rCellCount := ⟨by decide⟩
instance lobeDiagram_ofNat (n : ℕ) : OfNat lobeDiagram.toCombMap.Dart n :=
  inferInstanceAs (OfNat (Fin 10) n)
instance lobeDiagram_decidableEq : DecidableEq lobeDiagram.toCombMap.Dart :=
  inferInstanceAs (DecidableEq (Fin 10))

theorem lobeDiagram_cellDarts : Embedded.cellDarts lobeDiagram 0 = [0, 1, 2] := by
  change (boundary (face 0)).darts = _
  rw [boundary_face_darts]
  rfl

theorem lobeDiagram_outerDarts : Embedded.outerDarts lobeDiagram = [4, 6, 2] := by
  change ((boundary (face 3)).darts.reverse.map M.alpha) = _
  rw [boundary_face_darts]
  rfl

theorem lobe_empty_side_norm :
    WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal
      (Embedded.dartWord lobeDiagram ([] : List lobeDiagram.toCombMap.Dart))) ≤ 0 :=
  Nat.le_of_eq (WordMetric.wordNorm_one _)

/-! ## The pinched pocket face set -/

/-- The arc `[0, 1]` of `Π`. -/
noncomputable def pinchSourceArc : Embedded.CyclicArc (Embedded.cellDarts lobeDiagram 0) where
  start := ⟨0, Nat.succ_pos _⟩
  length := 2
  length_le := by
    rw [lobeDiagram_cellDarts]
    decide

theorem pinchSourceArc_darts : pinchSourceArc.darts = [0, 1] := by
  change ((Embedded.cellDarts lobeDiagram 0).drop 0 ++
    (Embedded.cellDarts lobeDiagram 0).take 0).take 2 = _
  rw [lobeDiagram_cellDarts]
  rfl

/-- The arc `[4, 6]` of the exterior boundary. -/
noncomputable def pinchTargetArc : Embedded.CyclicArc (Embedded.outerDarts lobeDiagram) where
  start := ⟨0, Nat.succ_pos _⟩
  length := 2
  length_le := by
    rw [lobeDiagram_outerDarts]
    decide

theorem pinchTargetArc_darts : pinchTargetArc.darts = [4, 6] := by
  change ((Embedded.outerDarts lobeDiagram).drop 0 ++
    (Embedded.outerDarts lobeDiagram).take 0).take 2 = _
  rw [lobeDiagram_outerDarts]
  rfl

theorem lobe_face_zero_not_mem_pinchFaces : face 0 ∉ pinchFaces := fun h =>
  (Finset.mem_cons.mp h).elim (fun h1 => absurd ((face_eq_iff 0 1).mp h1) (by decide))
    (fun h2 => absurd ((face_eq_iff 0 2).mp (Finset.mem_singleton.mp h2)) (by decide))

theorem lobe_face_three_not_mem_pinchFaces : face 3 ∉ pinchFaces := fun h =>
  (Finset.mem_cons.mp h).elim (fun h1 => absurd ((face_eq_iff 3 1).mp h1) (by decide))
    (fun h2 => absurd ((face_eq_iff 3 2).mp (Finset.mem_singleton.mp h2)) (by decide))

theorem lobe_face_one_mem_pinchFaces : face 1 ∈ pinchFaces := Finset.mem_cons.mpr (Or.inl rfl)

/-- The cycle of the pinched pocket is the reversed arc `[0, 1]` of `Π` and the arc `[4, 6]` of
the exterior, with empty sides. -/
theorem pinch_decomposition :
    (innerCycle : BoundaryCycle lobeDiagram.toCombMap pinchFaces).cycle =
      [] ++ Embedded.invDarts lobeDiagram pinchSourceArc.darts ++ [] ++ pinchTargetArc.darts := by
  rw [pinchSourceArc_darts, pinchTargetArc_darts]
  decide

/-- **The pinched pocket as a pocket face set.** -/
noncomputable def pinchedK : PocketFaceSet D 0 lobeDiagram 0 2 where
  faces := pinchFaces
  outerFace_not_mem := lobe_face_three_not_mem_pinchFaces
  source := 0
  source_not_mem := lobe_face_zero_not_mem_pinchFaces
  kept := ⟨1, by decide⟩
  kept_mem := lobe_face_one_mem_pinchFaces
  sourceArc := pinchSourceArc
  targetArc := pinchTargetArc
  firstSide := []
  secondSide := []
  boundary := innerCycle
  decomposition := pinch_decomposition
  firstSide_length_le := Nat.le_refl 0
  secondSide_length_le := Nat.le_refl 0
  firstSide_norm_le := lobe_empty_side_norm
  secondSide_norm_le := lobe_empty_side_norm
  lo_le := Nat.zero_le _
  le_hi := by decide

/-- The cycle of the pinched pocket does not follow the boundary. -/
theorem pinchedK_not_followsBoundary : ¬ pinchedK.boundary.FollowsBoundary :=
  not_followsBoundary

/-- The darts `3` and `6` of the pinched pocket start at one vertex. -/
theorem pinchedK_not_unpinched : ¬ Unpinched lobeDiagram.toCombMap pinchedK.faces := fun h =>
  absurd (h 3 6 ((innerBoundaryDart_iff 3).mpr (by decide))
    ((innerBoundaryDart_iff 6).mpr (by decide)) (vertexEquiv.injective (by decide))) (by decide)

/-- The pinched pocket is not simple. -/
theorem pinchedK_not_simple : ¬ pinchedK.Simple :=
  not_isSimpleClosedWalk

/-! ## The lobe `{a}` -/

/-- The face set `{a}`. -/
def lobeFaces : Finset lobeDiagram.toCombMap.Face := {face 1}

theorem face_mem_lobeFaces_iff (i : Fin 4) : face i ∈ lobeFaces ↔ i = 1 :=
  Finset.mem_singleton.trans (face_eq_iff i 1)

theorem lobeBoundaryDart_iff (d : Fin 10) :
    IsBoundaryDart lobeDiagram.toCombMap lobeFaces d ↔ d ∈ ([3, 4] : List (Fin 10)) := by
  change (M.faceOf d ∈ ({face 1} : Finset M.Face) ∧
    M.faceOf (M.alpha d) ∉ ({face 1} : Finset M.Face)) ↔ _
  simp only [Finset.mem_singleton, faceOf_eq_face]
  fin_cases d <;> decide

/-- The two boundary darts of the lobe. -/
def lobeCycle : BoundaryCycle lobeDiagram.toCombMap lobeFaces where
  cycle := ([3, 4] : List (Fin 10))
  cycle_nonempty := List.cons_ne_nil _ _
  cycle_nodup := (by decide : ([3, 4] : List (Fin 10)).Nodup)
  cycle_mem_iff := fun d => (lobeBoundaryDart_iff d).symm

/-- The arc `[0]` of `Π`. -/
def lobeSourceArc : Embedded.CyclicArc (Embedded.cellDarts lobeDiagram 0) where
  start := ⟨0, Nat.succ_pos _⟩
  length := 1
  length_le := by
    rw [lobeDiagram_cellDarts]
    decide

theorem lobeSourceArc_darts : lobeSourceArc.darts = [0] := by
  change ((Embedded.cellDarts lobeDiagram 0).drop 0 ++
    (Embedded.cellDarts lobeDiagram 0).take 0).take 1 = _
  rw [lobeDiagram_cellDarts]
  rfl

/-- The arc `[4]` of the exterior boundary. -/
def lobeTargetArc : Embedded.CyclicArc (Embedded.outerDarts lobeDiagram) where
  start := ⟨0, Nat.succ_pos _⟩
  length := 1
  length_le := by
    rw [lobeDiagram_outerDarts]
    decide

theorem lobeTargetArc_darts : lobeTargetArc.darts = [4] := by
  change ((Embedded.outerDarts lobeDiagram).drop 0 ++
    (Embedded.outerDarts lobeDiagram).take 0).take 1 = _
  rw [lobeDiagram_outerDarts]
  rfl

/-- The cycle of the lobe is the reversed arc `[0]` of `Π` and the arc `[4]` of the exterior, with
empty sides. -/
theorem lobe_decomposition :
    (lobeCycle : BoundaryCycle lobeDiagram.toCombMap lobeFaces).cycle =
      [] ++ Embedded.invDarts lobeDiagram lobeSourceArc.darts ++ [] ++ lobeTargetArc.darts := by
  rw [lobeSourceArc_darts, lobeTargetArc_darts]
  decide

/-- **The lobe as a pocket face set.** -/
noncomputable def lobeK : PocketFaceSet D 0 lobeDiagram 0 2 where
  faces := lobeFaces
  outerFace_not_mem := fun h => absurd ((face_mem_lobeFaces_iff 3).mp h) (by decide)
  source := 0
  source_not_mem := fun h => absurd ((face_mem_lobeFaces_iff 0).mp h) (by decide)
  kept := ⟨1, by decide⟩
  kept_mem := (face_mem_lobeFaces_iff 1).mpr rfl
  sourceArc := lobeSourceArc
  targetArc := lobeTargetArc
  firstSide := []
  secondSide := []
  boundary := lobeCycle
  decomposition := lobe_decomposition
  firstSide_length_le := Nat.le_refl 0
  secondSide_length_le := Nat.le_refl 0
  firstSide_norm_le := lobe_empty_side_norm
  secondSide_norm_le := lobe_empty_side_norm
  lo_le := Nat.zero_le _
  le_hi := by decide

theorem lobeFaces_subset : lobeFaces ⊆ pinchFaces :=
  Finset.singleton_subset_iff.mpr lobe_face_one_mem_pinchFaces

theorem lobeFaces_ne : lobeFaces ≠ pinchFaces := by
  intro h
  have h2 : face 2 ∈ pinchFaces := Finset.mem_cons.mpr (Or.inr (Finset.mem_singleton_self _))
  rw [← h] at h2
  exact absurd ((face_mem_lobeFaces_iff 2).mp h2) (by decide)

/-- **The cycle of the lobe is a simple closed walk.**  The dart `3` ends at the vertex `{0,4,7}`,
where `4` starts, and `4` ends at the vertex `{1,3,6,8}`, where `3` starts. -/
theorem lobeCycle_isSimpleClosedWalk :
    IsSimpleClosedWalk lobeDiagram.toCombMap ([3, 4] : List (Fin 10)) where
  ne_nil := List.cons_ne_nil _ _
  chain := List.isChain_pair.mpr (vertexEquiv.injective (by decide))
  closes := vertexEquiv.injective (by decide)
  vertex_nodup := by
    change [lobeDiagram.toCombMap.vertexOf (3 : Fin 10),
      lobeDiagram.toCombMap.vertexOf (4 : Fin 10)].Nodup
    exact List.nodup_cons.mpr ⟨fun h => absurd (congrArg vertexEquiv (List.mem_singleton.mp h))
      (by decide), List.nodup_singleton _⟩
  alpha_not_mem := by decide

/-- The lobe is simple. -/
theorem lobeK_simple : lobeK.Simple :=
  lobeCycle_isSimpleClosedWalk

/-! ## The lobe serves the pinched pocket -/

/-- **A lobe of a pinched pocket face set** (model test).  `lobeDiagram` has a pocket face set
between the positions `0` and `2` whose cycle does not both follow the boundary and stay
unpinched, and which is not simple.  Between the same positions it has a simple pocket face set on
a proper subset of those faces, with the same source and kept cells. -/
def PinchedPocketLobeModel : Prop :=
  ∃ K : PocketFaceSet D 0 lobeDiagram 0 2,
    ¬(K.boundary.FollowsBoundary ∧ Unpinched lobeDiagram.toCombMap K.faces) ∧ ¬ K.Simple ∧
      ∃ K' : PocketFaceSet D 0 lobeDiagram 0 2,
        K'.faces ⊆ K.faces ∧ K'.faces ≠ K.faces ∧ K'.source = K.source ∧ K'.kept = K.kept ∧
          K'.Simple

theorem pinchedPocketLobeModel : PinchedPocketLobeModel :=
  ⟨pinchedK, fun h => pinchedK_not_followsBoundary h.1, pinchedK_not_simple, lobeK,
    lobeFaces_subset, lobeFaces_ne, rfl, rfl, lobeK_simple⟩

/-- **The conclusion of `PocketPinchPinchedStatement` at `pinchedK`**, with the diagram itself as
the O-equivalent copy and the lobe as the simple pocket face set. -/
theorem pinchedPocketLobe_conclusion :
    ∃ (X' : DiscDiagram.{0, 0, 0} lobeW) (K' : PocketFaceSet D 0 X' 0 2),
      Nonempty (OEquivalentDiscDiagram lobeDiagram X') ∧ K'.Simple :=
  ⟨lobeDiagram, lobeK, ⟨OEquivalentDiscDiagram.refl lobeDiagram⟩, lobeK_simple⟩

#audit_axioms lobeDiagram
#audit_axioms pinchedK
#audit_axioms pinchedK_not_unpinched
#audit_axioms pinchedK_not_simple
#audit_axioms lobeK
#audit_closed_axioms lobeK_simple
#audit_closed_axioms pinchedPocketLobeModel
#audit_closed_axioms pinchedPocketLobe_conclusion

end GroupApproximation.GGT.VanKampen.OsinPocketPinchedTwoGonModel
