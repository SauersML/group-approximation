import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPieces
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketGapArcs
import GroupApproximation.Meta.AxiomGuard

/-!
# The face set between two exterior regions, for a simple boundary walk

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b):

> "Let us consider the subdiagram `Γ_1` of `Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2`, where
> `s_1, s_2` are side arcs of some of `Γ_{i,1}`'s and `t_1, t_2` are subpaths of `∂Π` and the
> section `q_1` of `∂Δ`, respectively; (ii) `Γ_1` contains all `Γ_{i,1}`'s."

This module proves two steps towards `SectionPocketFaceSetInput`.

* `CyclicArc.exists_spanArc`: two arcs of one carrier with disjoint darts, the first nonempty,
  are spanned by one arc with the start of the first: the first arc, a gap arc starting where
  the first arc ends, and the second arc.  This is `t_1` on `∂Π`.
* `PocketFaceSet.ofSimpleClosedWalk`: when the walk `s_1 t_1 s_2 t_2` is a simple closed walk
  with both arcs nonempty and a relator cell on its side, the faces on its side form a
  `PocketFaceSet`, with the walk as its boundary cycle.  The exterior face and the source cell
  lie across the arcs `t_2` and `t_1`, so both are outside.
* `PocketFaceSet.ofSimpleClosedWalk_simple`: that pocket face set is simple.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides

namespace Embedded.CyclicArc

/-- A nonempty arc has a dart. -/
theorem exists_mem_darts {Dart : Type v} {cycle : List Dart} (arc : CyclicArc cycle)
    (h : 0 < arc.length) : ∃ d, d ∈ arc.darts :=
  List.exists_mem_of_length_pos (by rw [arc.darts_length]; exact h)

/-- **The spanning arc.**  Two arcs of one carrier with disjoint darts, the first nonempty, are
spanned by an arc with the start of the first arc, whose darts are the first arc, a gap arc
starting where the first arc ends, and the second arc. -/
theorem exists_spanArc {Dart : Type v} {cycle : List Dart} (X Y : CyclicArc cycle)
    (hX : 0 < X.length) (hXY : ∀ d ∈ X.darts, d ∉ Y.darts) :
    ∃ Gap T : CyclicArc cycle, Gap.start = X.rest.start ∧ T.start = X.start ∧
      T.darts = X.darts ++ Gap.darts ++ Y.darts := by
  obtain ⟨G₁, G₂, hG₁, -, hrot⟩ := exists_gapArcs X Y hX hXY
  have hlen : (X.darts ++ G₁.darts ++ Y.darts).length ≤ cycle.length := by
    have h := congrArg List.length hrot
    simp only [List.length_append, X.rotated_length] at h
    simp only [List.length_append]
    omega
  refine ⟨G₁, ⟨X.start, (X.darts ++ G₁.darts ++ Y.darts).length, hlen⟩, hG₁, rfl, ?_⟩
  show X.rotated.take (X.darts ++ G₁.darts ++ Y.darts).length = _
  rw [hrot]
  exact List.take_append_length

end Embedded.CyclicArc

namespace PocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}
  {walk : List X.toCombMap.Dart}

/-- A simple closed walk through a dart of the oriented outer boundary keeps the exterior face
off its side: the exterior face lies across that dart. -/
theorem outerFace_not_mem_sideFaces (hw : IsSimpleClosedWalk X.toCombMap walk)
    {d : X.toCombMap.Dart} (hd : d ∈ walk) (hout : d ∈ outerDarts X) :
    X.outerFace ∉ sideFaces X.toCombMap walk := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hout
  have hface : X.toCombMap.faceOf e = X.outerFace :=
    ((X.faceBoundary X.outerFace).mem_iff e).mp (List.mem_reverse.mp he)
  have h := And.right ((hw.isBoundaryDart_sideFaces_iff X.planar _).mpr hd)
  rwa [X.toCombMap.alpha_involutive e, hface] at h

/-- A simple closed walk through the reverse of a dart of a relator cell keeps that cell off its
side: the cell lies across that dart. -/
theorem cell_face_not_mem_sideFaces (hw : IsSimpleClosedWalk X.toCombMap walk)
    {i : Fin X.rCellCount} {e : X.toCombMap.Dart} (he : e ∈ cellDarts X i)
    (hd : X.toCombMap.alpha e ∈ walk) : (cell X i).face ∉ sideFaces X.toCombMap walk := by
  have hface : X.toCombMap.faceOf e = (cell X i).face :=
    ((X.faceBoundary (cell X i).face).mem_iff e).mp he
  have h := And.right ((hw.isBoundaryDart_sideFaces_iff X.planar _).mpr hd)
  rwa [X.toCombMap.alpha_involutive e, hface] at h

/-- **The pocket face set of a simple boundary walk.**  Let `s_1 t_1 s_2 t_2` be a simple closed
walk, with `t_1` a nonempty arc of the cell `source` read backwards, `t_2` a nonempty arc of `∂X`
between the positions `lo` and `hi`, and sides no longer than `ε` with values no longer than
`ε`.  When the cell `kept` lies on the walk's side, the faces on that side form a pocket face set
whose boundary cycle is the walk. -/
noncomputable def ofSimpleClosedWalk (source kept : Fin X.rCellCount)
    (sourceArc : CyclicArc (cellDarts X source)) (targetArc : CyclicArc (outerDarts X))
    (firstSide secondSide : List X.toCombMap.Dart)
    (hw : IsSimpleClosedWalk X.toCombMap
      (firstSide ++ invDarts X sourceArc.darts ++ secondSide ++ targetArc.darts))
    (hsource : 0 < sourceArc.length) (htarget : 0 < targetArc.length)
    (hkept : (cell X kept).face ∈ sideFaces X.toCombMap
      (firstSide ++ invDarts X sourceArc.darts ++ secondSide ++ targetArc.darts))
    (hfirst : firstSide.length ≤ eps) (hsecond : secondSide.length ≤ eps)
    (hfirstNorm :
      wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X firstSide)) ≤ eps)
    (hsecondNorm :
      wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X secondSide)) ≤ eps)
    (hlo : lo ≤ targetArc.start.1) (hhi : targetArc.start.1 + targetArc.length ≤ hi) :
    PocketFaceSet D eps X lo hi where
  faces := sideFaces X.toCombMap
    (firstSide ++ invDarts X sourceArc.darts ++ secondSide ++ targetArc.darts)
  outerFace_not_mem := by
    obtain ⟨d, hd⟩ := targetArc.exists_mem_darts htarget
    exact outerFace_not_mem_sideFaces hw (List.mem_append_right _ hd)
      (targetArc.mem_cycle_of_mem_darts hd)
  source := source
  source_not_mem := by
    obtain ⟨e, he⟩ := sourceArc.exists_mem_darts hsource
    have hinv : X.toCombMap.alpha e ∈ invDarts X sourceArc.darts :=
      List.mem_map_of_mem (List.mem_reverse.mpr he)
    exact cell_face_not_mem_sideFaces hw (sourceArc.mem_cycle_of_mem_darts he)
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hinv)))
  kept := kept
  kept_mem := hkept
  sourceArc := sourceArc
  targetArc := targetArc
  firstSide := firstSide
  secondSide := secondSide
  boundary := hw.innerCycle X.planar
  decomposition := rfl
  firstSide_length_le := hfirst
  secondSide_length_le := hsecond
  firstSide_norm_le := hfirstNorm
  secondSide_norm_le := hsecondNorm
  lo_le := hlo
  le_hi := hhi

/-- The pocket face set of a simple boundary walk is simple. -/
theorem ofSimpleClosedWalk_simple (source kept : Fin X.rCellCount)
    (sourceArc : CyclicArc (cellDarts X source)) (targetArc : CyclicArc (outerDarts X))
    (firstSide secondSide : List X.toCombMap.Dart)
    (hw : IsSimpleClosedWalk X.toCombMap
      (firstSide ++ invDarts X sourceArc.darts ++ secondSide ++ targetArc.darts))
    (hsource : 0 < sourceArc.length) (htarget : 0 < targetArc.length)
    (hkept : (cell X kept).face ∈ sideFaces X.toCombMap
      (firstSide ++ invDarts X sourceArc.darts ++ secondSide ++ targetArc.darts))
    (hfirst : firstSide.length ≤ eps) (hsecond : secondSide.length ≤ eps)
    (hfirstNorm :
      wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X firstSide)) ≤ eps)
    (hsecondNorm :
      wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X secondSide)) ≤ eps)
    (hlo : lo ≤ targetArc.start.1) (hhi : targetArc.start.1 + targetArc.length ≤ hi) :
    (ofSimpleClosedWalk (D := D) source kept sourceArc targetArc firstSide secondSide hw hsource
      htarget hkept hfirst hsecond hfirstNorm hsecondNorm hlo hhi).Simple :=
  hw

end PocketFaceSet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.exists_spanArc
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.outerFace_not_mem_sideFaces
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.cell_face_not_mem_sideFaces
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.ofSimpleClosedWalk_simple
