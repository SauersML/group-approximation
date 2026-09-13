import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPieces
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketGapArcs
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# The face set between two exterior regions, for a simple boundary walk

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b):

> "Let us consider the subdiagram `Γ_1` of `Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2`, where
> `s_1, s_2` are side arcs of some of `Γ_{i,1}`'s and `t_1, t_2` are subpaths of `∂Π` and the
> section `q_1` of `∂Δ`, respectively; (ii) `Γ_1` contains all `Γ_{i,1}`'s."

This module proves steps towards `SectionPocketFaceSetInput`.

* `CyclicArc.exists_spanArc`: two arcs of one carrier with disjoint darts, the first nonempty,
  are spanned by one arc with the start of the first: the first arc, a gap arc starting where
  the first arc ends, and the second arc.  This is `t_1` on `∂Π`.
* `PocketFaceSet.ofSimpleClosedWalk`: when the walk `s_1 t_1 s_2 t_2` is a simple closed walk
  with both arcs nonempty and a relator cell on its side, the faces on its side form a
  `PocketFaceSet`, with the walk as its boundary cycle.  The exterior face and the source cell
  lie across the arcs `t_2` and `t_1`, so both are outside.
* `PocketFaceSet.ofSimpleClosedWalk_simple`: that pocket face set is simple.
* `PocketWalk.exists_of_exteriorAt`: two distinct exterior regions of one cell to one section
  give the walk data `s_1 t_1 s_2 t_2` in the positions of the section.  The region whose outer
  arc starts first is `x`.  `s_1` is the left side of the other region `y`, `t_1` spans the
  source arcs of `x` and `y`, `s_2` is the right side of `x`, and `t_2` runs on `∂Δ` from the
  start of `x`'s outer arc to the end of `y`'s.
* `PocketWalk.toPocketFaceSet`: a simple pocket walk with a relator cell on its side gives a
  `PocketFaceSet`.
* `PocketFaceSet.ofBoundaryCycle`: a face set with boundary cycle `s_1 t_1 s_2 t_2` that contains a
  relator cell is a `PocketFaceSet`.  A boundary dart has its own face inside and the face across
  it outside, so the exterior face and the source cell, which lie across `t_2` and `t_1`, are
  outside.
* `PocketWalk.toPocketFaceSetOfNoncrossing`: a noncrossing pocket walk (`IsNoncrossingClosedWalk`,
  which lets the walk touch itself at a vertex) with a relator cell on its side gives a
  `PocketFaceSet` with the walk as its boundary cycle, in walk order
  (`toPocketFaceSetOfNoncrossing_closedWalk`).

Not proved here: that the pocket walk is noncrossing, and that a relator cell lies on its side.

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

/-- An arc of a carrier indexed by `a₁` is an arc of the same carrier indexed by `a₂ = a₁`, with
the same start, length and darts. -/
theorem exists_transport {α : Type*} {Dart : Type v} (f : α → List Dart) {a₁ a₂ : α}
    (h : a₁ = a₂) (arc : CyclicArc (f a₁)) :
    ∃ arc' : CyclicArc (f a₂), arc'.start.1 = arc.start.1 ∧ arc'.length = arc.length ∧
      arc'.darts = arc.darts := by
  subst h
  exact ⟨arc, rfl, rfl, rfl⟩

end Embedded.CyclicArc

namespace PocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}
  {walk : List X.toCombMap.Dart}

/-- A simple closed walk through a dart of the oriented outer boundary keeps the exterior face
off its side: the exterior face lies across that dart. -/
theorem outerFace_not_mem_sideFaces_of_mem_outerDarts (hw : IsSimpleClosedWalk X.toCombMap walk)
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
    exact outerFace_not_mem_sideFaces_of_mem_outerDarts hw (List.mem_append_right _ hd)
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

/-- **The pocket face set of a boundary cycle.**  Let `faces` have the boundary cycle
`s_1 t_1 s_2 t_2`, with `t_1` a nonempty arc of the cell `source` read backwards, `t_2` a nonempty
arc of `∂X` between the positions `lo` and `hi`, and sides no longer than `ε` with values no
longer than `ε`.  When `faces` contains the cell `kept`, it is a pocket face set with that
boundary cycle. -/
noncomputable def ofBoundaryCycle {faces : Finset X.toCombMap.Face}
    (boundary : Surgery.MapCollapse.BoundaryCycle X.toCombMap faces)
    (source kept : Fin X.rCellCount)
    (sourceArc : CyclicArc (cellDarts X source)) (targetArc : CyclicArc (outerDarts X))
    (firstSide secondSide : List X.toCombMap.Dart)
    (hcycle : boundary.cycle =
      firstSide ++ invDarts X sourceArc.darts ++ secondSide ++ targetArc.darts)
    (hsource : 0 < sourceArc.length) (htarget : 0 < targetArc.length)
    (hkept : (cell X kept).face ∈ faces)
    (hfirst : firstSide.length ≤ eps) (hsecond : secondSide.length ≤ eps)
    (hfirstNorm :
      wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X firstSide)) ≤ eps)
    (hsecondNorm :
      wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X secondSide)) ≤ eps)
    (hlo : lo ≤ targetArc.start.1) (hhi : targetArc.start.1 + targetArc.length ≤ hi) :
    PocketFaceSet D eps X lo hi where
  faces := faces
  outerFace_not_mem := by
    obtain ⟨d, hd⟩ := targetArc.exists_mem_darts htarget
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (targetArc.mem_cycle_of_mem_darts hd)
    have hface : X.toCombMap.faceOf e = X.outerFace :=
      ((X.faceBoundary X.outerFace).mem_iff e).mp (List.mem_reverse.mp he)
    have hmem : X.toCombMap.alpha e ∈ boundary.cycle := by
      rw [hcycle]
      exact List.mem_append_right _ hd
    have h := And.right ((boundary.cycle_mem_iff (X.toCombMap.alpha e)).mp hmem)
    rwa [X.toCombMap.alpha_involutive e, hface] at h
  source := source
  source_not_mem := by
    obtain ⟨e, he⟩ := sourceArc.exists_mem_darts hsource
    have hface : X.toCombMap.faceOf e = (cell X source).face :=
      ((X.faceBoundary (cell X source).face).mem_iff e).mp (sourceArc.mem_cycle_of_mem_darts he)
    have hinv : X.toCombMap.alpha e ∈ invDarts X sourceArc.darts :=
      List.mem_map_of_mem (List.mem_reverse.mpr he)
    have hmem : X.toCombMap.alpha e ∈ boundary.cycle := by
      rw [hcycle]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hinv))
    have h := And.right ((boundary.cycle_mem_iff (X.toCombMap.alpha e)).mp hmem)
    rwa [X.toCombMap.alpha_involutive e, hface] at h
  kept := kept
  kept_mem := hkept
  sourceArc := sourceArc
  targetArc := targetArc
  firstSide := firstSide
  secondSide := secondSide
  boundary := boundary
  decomposition := hcycle
  firstSide_length_le := hfirst
  secondSide_length_le := hsecond
  firstSide_norm_le := hfirstNorm
  secondSide_norm_le := hsecondNorm
  lo_le := hlo
  le_hi := hhi

/-- **The pocket face set of a noncrossing boundary walk.**  As `ofSimpleClosedWalk`, for a walk
`s_1 t_1 s_2 t_2` that may touch itself at a vertex without crossing. -/
noncomputable def ofNoncrossingClosedWalk (source kept : Fin X.rCellCount)
    (sourceArc : CyclicArc (cellDarts X source)) (targetArc : CyclicArc (outerDarts X))
    (firstSide secondSide : List X.toCombMap.Dart)
    (hw : IsNoncrossingClosedWalk X.toCombMap
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
    PocketFaceSet D eps X lo hi :=
  ofBoundaryCycle (hw.innerCycle X.planar) source kept sourceArc targetArc firstSide secondSide
    rfl hsource htarget hkept hfirst hsecond hfirstNorm hsecondNorm hlo hhi

end PocketFaceSet

/-! ## The pocket walk of two exterior regions -/

section Walk

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **The pocket walk data** (Osin's `s_1 t_1 s_2 t_2`): a nonempty arc `t_1` of the cell
`source`, a nonempty arc `t_2` of `∂X` between the positions `lo` and `hi`, and two sides no
longer than `ε` with values no longer than `ε`. -/
structure PocketWalk (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    (lo hi : ℕ) where
  source : Fin X.rCellCount
  sourceArc : CyclicArc (cellDarts X source)
  targetArc : CyclicArc (outerDarts X)
  firstSide : List X.toCombMap.Dart
  secondSide : List X.toCombMap.Dart
  sourceArc_pos : 0 < sourceArc.length
  targetArc_pos : 0 < targetArc.length
  firstSide_length_le : firstSide.length ≤ eps
  secondSide_length_le : secondSide.length ≤ eps
  firstSide_norm_le :
    wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X firstSide)) ≤ eps
  secondSide_norm_le :
    wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X secondSide)) ≤ eps
  lo_le : lo ≤ targetArc.start.1
  le_hi : targetArc.start.1 + targetArc.length ≤ hi

namespace PocketWalk

variable {D : RelGenSet G Lambda} {eps : ℕ}

section Diagram

variable {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- The walk `s_1 t_1 s_2 t_2`, with `t_1` read backwards. -/
def walk (K : PocketWalk D eps X lo hi) : List X.toCombMap.Dart :=
  K.firstSide ++ invDarts X K.sourceArc.darts ++ K.secondSide ++ K.targetArc.darts

/-- A simple pocket walk with a relator cell on its side gives a pocket face set. -/
noncomputable def toPocketFaceSet (K : PocketWalk D eps X lo hi) (kept : Fin X.rCellCount)
    (hw : IsSimpleClosedWalk X.toCombMap K.walk)
    (hkept : (cell X kept).face ∈ sideFaces X.toCombMap K.walk) :
    PocketFaceSet D eps X lo hi :=
  PocketFaceSet.ofSimpleClosedWalk K.source kept K.sourceArc K.targetArc K.firstSide
    K.secondSide hw K.sourceArc_pos K.targetArc_pos hkept K.firstSide_length_le
    K.secondSide_length_le K.firstSide_norm_le K.secondSide_norm_le K.lo_le K.le_hi

theorem toPocketFaceSet_simple (K : PocketWalk D eps X lo hi) (kept : Fin X.rCellCount)
    (hw : IsSimpleClosedWalk X.toCombMap K.walk)
    (hkept : (cell X kept).face ∈ sideFaces X.toCombMap K.walk) :
    (K.toPocketFaceSet kept hw hkept).Simple :=
  hw

/-- A noncrossing pocket walk with a relator cell on its side gives a pocket face set. -/
noncomputable def toPocketFaceSetOfNoncrossing (K : PocketWalk D eps X lo hi)
    (kept : Fin X.rCellCount) (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    (hkept : (cell X kept).face ∈ sideFaces X.toCombMap K.walk) :
    PocketFaceSet D eps X lo hi :=
  PocketFaceSet.ofNoncrossingClosedWalk K.source kept K.sourceArc K.targetArc K.firstSide
    K.secondSide hw K.sourceArc_pos K.targetArc_pos hkept K.firstSide_length_le
    K.secondSide_length_le K.firstSide_norm_le K.secondSide_norm_le K.lo_le K.le_hi

/-- The pocket face set of a noncrossing pocket walk has the walk as its boundary cycle. -/
theorem toPocketFaceSetOfNoncrossing_cycle (K : PocketWalk D eps X lo hi)
    (kept : Fin X.rCellCount) (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    (hkept : (cell X kept).face ∈ sideFaces X.toCombMap K.walk) :
    (K.toPocketFaceSetOfNoncrossing kept hw hkept).boundary.cycle = K.walk :=
  rfl

/-- The pocket face set of a noncrossing pocket walk is in walk order: its boundary cycle is the
walk, so the `chain` and `closes` fields of the walk make it a closed walk. -/
theorem toPocketFaceSetOfNoncrossing_closedWalk (K : PocketWalk D eps X lo hi)
    (kept : Fin X.rCellCount) (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    (hkept : (cell X kept).face ∈ sideFaces X.toCombMap K.walk) :
    (K.toPocketFaceSetOfNoncrossing kept hw hkept).ClosedWalk :=
  ⟨hw.chain, hw.closes⟩

end Diagram

variable {Delta : DiscDiagram.{u, w, v} W} {lambda c : ℝ}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- A position of a section of `∂Δ` is a position of the oriented outer boundary of the diagram
of a realized family. -/
theorem cut_le_length_outerDarts (S : RealizedSectionFamily D lambda c eps Delta cuts)
    (k : Fin (cuts.count + 1)) : cuts.cut k ≤ (outerDarts S.diagram).length := by
  have hlen : (outerDarts S.diagram).length = Delta.boundaryWord.length := by
    rw [← S.equiv.boundaryWord_eq, ← dartWord_outerDarts S.diagram, dartWord, List.length_map]
  exact Nat.le_trans (cuts.cut_mono (Fin.le_last k))
    (Nat.le_of_eq (cuts.cut_last.trans hlen.symm))

/-- **The pocket walk of two ordered exterior regions.**  Two distinct exterior regions `x`, `y`
of the cell `i` to section `j`, with the target arc of `x` starting no later than that of `y`,
give a pocket walk: `y`'s left side, the arc of `Π_i` spanning the source arcs of `x`, a gap and
`y`, read backwards, `x`'s right side, and the arc of `∂Δ` from the start of `x`'s target arc to
the end of `y`'s. -/
theorem exists_of_le (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {j : Fin cuts.count} {x y : RegionCandidate D eps S.diagram}
    (hx : x ∈ RegionCandidate.exteriorAt S.family i)
    (hy : y ∈ RegionCandidate.exteriorAt S.family i) (hxy : x ≠ y)
    (hjx : RegionCandidate.TargetsSectionIndex cuts j x)
    (hjy : RegionCandidate.TargetsSectionIndex cuts j y)
    (hle : x.2.targetArc.start.1 ≤ y.2.targetArc.start.1) :
    ∃ K : PocketWalk D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ),
      K.source = i ∧ K.firstSide = y.2.leftSide ∧ K.secondSide = x.2.rightSide ∧
        (∃ Gap : CyclicArc (cellDarts S.diagram i),
          K.sourceArc.darts = x.2.sourceArc.darts ++ Gap.darts ++ y.2.sourceArc.darts) ∧
        K.targetArc.start.1 = x.2.targetArc.start.1 ∧
        K.targetArc.start.1 + K.targetArc.length =
          y.2.targetArc.start.1 + y.2.targetArc.length := by
  obtain ⟨hxK, hxi⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyK, hyi⟩ := Finset.mem_filter.mp hy
  have hxS : x ∈ S.family := (Finset.mem_filter.mp hxK).1
  have hyS : y ∈ S.family := (Finset.mem_filter.mp hyK).1
  obtain ⟨hxsrc, -⟩ := S.nondegenerate x hxS
  obtain ⟨-, hytgt⟩ := S.nondegenerate y hyS
  obtain ⟨-, hxlo, hxhi⟩ := hjx
  obtain ⟨-, -, hyhi⟩ := hjy
  obtain ⟨X, -, hXl, hXd⟩ := CyclicArc.exists_transport (cellDarts S.diagram) hxi x.2.sourceArc
  obtain ⟨Y, -, -, hYd⟩ := CyclicArc.exists_transport (cellDarts S.diagram) hyi y.2.sourceArc
  have hXY : ∀ d ∈ X.darts, d ∉ Y.darts := by
    intro d hdX hdY
    rw [hXd] at hdX
    rw [hYd] at hdY
    exact Finset.disjoint_left.mp (S.pairwise x hxS y hyS hxy)
      (x.2.faceOf_alpha_mem_of_mem_sourceArc d hdX) (y.2.faceOf_alpha_mem_of_mem_sourceArc d hdY)
  obtain ⟨Gap, T, -, -, hT⟩ := CyclicArc.exists_spanArc X Y (by rw [hXl]; exact hxsrc) hXY
  have hTl : 0 < T.length := by
    have h := congrArg List.length hT
    simp only [List.length_append, T.darts_length, X.darts_length] at h
    omega
  rw [hXd, hYd] at hT
  have hn := cut_le_length_outerDarts S j.succ
  obtain ⟨t₂, ht₂s, ht₂l⟩ : ∃ t₂ : CyclicArc (outerDarts S.diagram),
      t₂.start.1 = x.2.targetArc.start.1 ∧
        t₂.length = y.2.targetArc.start.1 + y.2.targetArc.length - x.2.targetArc.start.1 :=
    ⟨⟨⟨x.2.targetArc.start.1, by omega⟩,
      y.2.targetArc.start.1 + y.2.targetArc.length - x.2.targetArc.start.1, by omega⟩, rfl, rfl⟩
  have hend : t₂.start.1 + t₂.length = y.2.targetArc.start.1 + y.2.targetArc.length := by
    omega
  refine ⟨
    { source := i
      sourceArc := T
      targetArc := t₂
      firstSide := y.2.leftSide
      secondSide := x.2.rightSide
      sourceArc_pos := hTl
      targetArc_pos := by omega
      firstSide_length_le := y.2.leftSide_length_le
      secondSide_length_le := x.2.rightSide_length_le
      firstSide_norm_le := y.2.leftSide_norm_le
      secondSide_norm_le := x.2.rightSide_norm_le
      lo_le := by omega
      le_hi := by omega }, rfl, rfl, rfl, ⟨Gap, hT⟩, ht₂s, hend⟩

/-- **The pocket walk of two exterior regions.**  Two distinct exterior regions of the cell `i`
to section `j`, ordered as `x`, `y` by the start of their target arcs, give a pocket walk in the
positions of section `j`: `y`'s left side, the arc of `Π_i` spanning the source arcs of `x`, a gap
and `y`, read backwards, `x`'s right side, and the arc of `∂Δ` from the start of `x`'s target arc
to the end of `y`'s. -/
theorem exists_of_exteriorAt (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {j : Fin cuts.count} {a b : RegionCandidate D eps S.diagram}
    (ha : a ∈ RegionCandidate.exteriorAt S.family i)
    (hb : b ∈ RegionCandidate.exteriorAt S.family i) (hab : a ≠ b)
    (hja : RegionCandidate.TargetsSectionIndex cuts j a)
    (hjb : RegionCandidate.TargetsSectionIndex cuts j b) :
    ∃ (K : PocketWalk D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ))
      (x y : RegionCandidate D eps S.diagram), (x = a ∧ y = b ∨ x = b ∧ y = a) ∧
      K.source = i ∧ K.firstSide = y.2.leftSide ∧ K.secondSide = x.2.rightSide ∧
        (∃ Gap : CyclicArc (cellDarts S.diagram i),
          K.sourceArc.darts = x.2.sourceArc.darts ++ Gap.darts ++ y.2.sourceArc.darts) ∧
        K.targetArc.start.1 = x.2.targetArc.start.1 ∧
        K.targetArc.start.1 + K.targetArc.length =
          y.2.targetArc.start.1 + y.2.targetArc.length := by
  by_cases hle : a.2.targetArc.start.1 ≤ b.2.targetArc.start.1
  · obtain ⟨K, hK⟩ := exists_of_le S ha hb hab hja hjb hle
    exact ⟨K, a, b, Or.inl ⟨rfl, rfl⟩, hK⟩
  · obtain ⟨K, hK⟩ := exists_of_le S hb ha (Ne.symm hab) hjb hja (by omega)
    exact ⟨K, b, a, Or.inr ⟨rfl, rfl⟩, hK⟩

end PocketWalk

end Walk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.exists_spanArc
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.outerFace_not_mem_sideFaces_of_mem_outerDarts
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.cell_face_not_mem_sideFaces
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.ofSimpleClosedWalk_simple
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.exists_transport
#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalk.toPocketFaceSet_simple
#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalk.cut_le_length_outerDarts
#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalk.exists_of_exteriorAt
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.ofBoundaryCycle
#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalk.toPocketFaceSetOfNoncrossing_cycle
#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalk.toPocketFaceSetOfNoncrossing_closedWalk
