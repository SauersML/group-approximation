import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketOuterSpur
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellTransport
import GroupApproximation.Meta.AxiomGuard

/-!
# The pocket between two cells across the thickening of an outer spur

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2` between two regions joining the cells `Π_i` and `Π_j`.  A vertex split
outside the face set merges two G-faces, so a corner in the exterior is first filled with a G-cell
digon by thickening an outer edge (`OuterSpurThickening.diagram`).  The thickening keeps every old
dart, label, vertex and relator cell, and the relator words.  A cell pocket has no arc on the
exterior boundary, so its face set, both cells, the kept cell, the arcs, the sides and the boundary
cycle transport by the dart embedding with no avoidance hypothesis.

* `CellPocketFaceSet.outerSpurThickening`: the transported cell pocket face set.
* `outerSpurThickening_closedWalk`, `outerSpurThickening_repeatedVisits`: walk order and the repeated
  visits are unchanged.
* `outerSpurThickening_first_proper`, `outerSpurThickening_second_proper`: both arcs stay proper.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

namespace CellPocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **The cell pocket face set across the thickening of an outer spur**: the image faces and cells,
with the boundary cycle, the arcs and the sides mapped by the dart embedding. -/
noncomputable def outerSpurThickening (K : CellPocketFaceSet D eps X i j)
    (k : Fin (X.faceBoundary X.outerFace).darts.length)
    (hlen : 1 < (X.faceBoundary X.outerFace).darts.length) :
    CellPocketFaceSet D eps (OuterSpurThickening.diagram X k hlen)
      ((OuterSpurThickening.cellMap X k hlen).indexEquiv i)
      ((OuterSpurThickening.cellMap X k hlen).indexEquiv j) where
  faces := (OuterSpurThickening.embedding X k hlen).faceSet K.faces
  outerFace_not_mem := by
    change (OuterSpurThickening.diagram X k hlen).outerFace ∉
      K.faces.map (OuterSpurThickening.embedding X k hlen).faces
    rw [(OuterSpurThickening.embedding X k hlen).outer, Finset.mem_map']
    exact K.outerFace_not_mem
  first_not_mem := by
    rw [(OuterSpurThickening.cellMap X k hlen).indexed_cell i,
      (OuterSpurThickening.cellMap X k hlen).face_eq]
    change (OuterSpurThickening.embedding X k hlen).faces (Embedded.cell X i).face ∉
      K.faces.map (OuterSpurThickening.embedding X k hlen).faces
    rw [Finset.mem_map']
    exact K.first_not_mem
  second_not_mem := by
    rw [(OuterSpurThickening.cellMap X k hlen).indexed_cell j,
      (OuterSpurThickening.cellMap X k hlen).face_eq]
    change (OuterSpurThickening.embedding X k hlen).faces (Embedded.cell X j).face ∉
      K.faces.map (OuterSpurThickening.embedding X k hlen).faces
    rw [Finset.mem_map']
    exact K.second_not_mem
  kept := (OuterSpurThickening.cellMap X k hlen).indexEquiv K.kept
  kept_mem := by
    rw [(OuterSpurThickening.cellMap X k hlen).indexed_cell K.kept,
      (OuterSpurThickening.cellMap X k hlen).face_eq]
    change (OuterSpurThickening.embedding X k hlen).faces (Embedded.cell X K.kept).face ∈
      K.faces.map (OuterSpurThickening.embedding X k hlen).faces
    rw [Finset.mem_map']
    exact K.kept_mem
  firstArc := K.firstArc.mapTo (OuterSpurThickening.embedding X k hlen).darts
    (OuterSpurThickening.cellDarts_eq X k hlen i)
  secondArc := K.secondArc.mapTo (OuterSpurThickening.embedding X k hlen).darts
    (OuterSpurThickening.cellDarts_eq X k hlen j)
  firstSide := K.firstSide.map (OuterSpurThickening.embedding X k hlen).darts
  secondSide := K.secondSide.map (OuterSpurThickening.embedding X k hlen).darts
  boundary := (OuterSpurThickening.embedding X k hlen).boundaryCycle K.faces
    K.outerFace_not_mem K.boundary
  decomposition := by
    change K.boundary.cycle.map (OuterSpurThickening.embedding X k hlen).darts = _
    rw [CyclicArc.mapTo_darts K.firstArc (OuterSpurThickening.embedding X k hlen).darts
        (OuterSpurThickening.cellDarts_eq X k hlen i),
      CyclicArc.mapTo_darts K.secondArc (OuterSpurThickening.embedding X k hlen).darts
        (OuterSpurThickening.cellDarts_eq X k hlen j),
      DiscEmbeddingAway.invDarts_map, DiscEmbeddingAway.invDarts_map, K.decomposition]
    simp only [List.map_append]
  firstArc_pos := by
    rw [CyclicArc.mapTo_length]
    exact K.firstArc_pos
  secondArc_pos := by
    rw [CyclicArc.mapTo_length]
    exact K.secondArc_pos
  firstSide_length_le := by
    rw [List.length_map]
    exact K.firstSide_length_le
  secondSide_length_le := by
    rw [List.length_map]
    exact K.secondSide_length_le
  firstSide_norm_le := by
    rw [DiscEmbeddingAway.dartWord_map]
    exact K.firstSide_norm_le
  secondSide_norm_le := by
    rw [DiscEmbeddingAway.dartWord_map]
    exact K.secondSide_norm_le

section Thickening

variable (K : CellPocketFaceSet D eps X i j) (k : Fin (X.faceBoundary X.outerFace).darts.length)
  (hlen : 1 < (X.faceBoundary X.outerFace).darts.length)

theorem outerSpurThickening_boundary_cycle :
    (K.outerSpurThickening k hlen).boundary.cycle =
      K.boundary.cycle.map (OuterSpurThickening.embedding X k hlen).darts :=
  rfl

/-- **The thickening keeps walk order.** -/
theorem outerSpurThickening_closedWalk (hK : K.ClosedWalk) :
    (K.outerSpurThickening k hlen).ClosedWalk := by
  refine ⟨?_, ?_⟩
  · change (K.boundary.cycle.map (OuterSpurThickening.embedding X k hlen).darts).IsChain
      (fun d e => (OuterSpurThickening.diagram X k hlen).toCombMap.vertexOf
        ((OuterSpurThickening.diagram X k hlen).toCombMap.alpha d) =
          (OuterSpurThickening.diagram X k hlen).toCombMap.vertexOf e)
    exact (List.isChain_map _).mpr (hK.1.imp fun d e h =>
      (OuterSpurThickening.vertexOf_alpha_embedding_eq_iff X k hlen d e).mpr h)
  · change (OuterSpurThickening.diagram X k hlen).toCombMap.vertexOf
        ((OuterSpurThickening.diagram X k hlen).toCombMap.alpha
          ((K.boundary.cycle.map (OuterSpurThickening.embedding X k hlen).darts).getLast
            (K.outerSpurThickening k hlen).boundary.cycle_nonempty)) =
      (OuterSpurThickening.diagram X k hlen).toCombMap.vertexOf
        ((K.boundary.cycle.map (OuterSpurThickening.embedding X k hlen).darts).head
          (K.outerSpurThickening k hlen).boundary.cycle_nonempty)
    rw [List.getLast_map, List.head_map]
    exact (OuterSpurThickening.vertexOf_alpha_embedding_eq_iff X k hlen _ _).mpr hK.2

/-- **The thickening keeps the repeated visits.** -/
theorem outerSpurThickening_repeatedVisits :
    (K.outerSpurThickening k hlen).repeatedVisits = K.repeatedVisits := by
  unfold CellPocketFaceSet.repeatedVisits
  rw [outerSpurThickening_boundary_cycle, List.length_map, List.map_map]
  congr 1
  exact card_toFinset_map_eq_of_iff
    ((OuterSpurThickening.diagram X k hlen).toCombMap.vertexOf ∘
      (OuterSpurThickening.embedding X k hlen).darts)
    X.toCombMap.vertexOf
    (fun a b => OuterSpurThickening.vertexOf_embedding_eq_iff X k hlen a b) _

/-- **The first arc stays proper.** -/
theorem outerSpurThickening_first_proper (hfirst : K.firstArc.length < (cellDarts X i).length) :
    (K.outerSpurThickening k hlen).firstArc.length <
      (cellDarts (OuterSpurThickening.diagram X k hlen)
        ((OuterSpurThickening.cellMap X k hlen).indexEquiv i)).length := by
  have h1 : (K.outerSpurThickening k hlen).firstArc.length = K.firstArc.length :=
    CyclicArc.mapTo_length K.firstArc _ (OuterSpurThickening.cellDarts_eq X k hlen i)
  have h2 : (cellDarts (OuterSpurThickening.diagram X k hlen)
      ((OuterSpurThickening.cellMap X k hlen).indexEquiv i)).length = (cellDarts X i).length :=
    (congrArg List.length (OuterSpurThickening.cellDarts_eq X k hlen i)).trans (List.length_map _)
  exact lt_of_eq_of_lt h1 (lt_of_lt_of_eq hfirst h2.symm)

/-- **The second arc stays proper.** -/
theorem outerSpurThickening_second_proper (hsecond : K.secondArc.length < (cellDarts X j).length) :
    (K.outerSpurThickening k hlen).secondArc.length <
      (cellDarts (OuterSpurThickening.diagram X k hlen)
        ((OuterSpurThickening.cellMap X k hlen).indexEquiv j)).length := by
  have h1 : (K.outerSpurThickening k hlen).secondArc.length = K.secondArc.length :=
    CyclicArc.mapTo_length K.secondArc _ (OuterSpurThickening.cellDarts_eq X k hlen j)
  have h2 : (cellDarts (OuterSpurThickening.diagram X k hlen)
      ((OuterSpurThickening.cellMap X k hlen).indexEquiv j)).length = (cellDarts X j).length :=
    (congrArg List.length (OuterSpurThickening.cellDarts_eq X k hlen j)).trans (List.length_map _)
  exact lt_of_eq_of_lt h1 (lt_of_lt_of_eq hsecond h2.symm)

end Thickening

end CellPocketFaceSet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.outerSpurThickening
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.outerSpurThickening_closedWalk
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.outerSpurThickening_repeatedVisits
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.outerSpurThickening_first_proper
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.outerSpurThickening_second_proper
