import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFaceSetOnCopy
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketKeptCell
import GroupApproximation.GGT.VanKampen.FaceShellingValue
import GroupApproximation.Meta.AxiomGuard

/-!
# The inner pocket between two exterior regions

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with `∂Γ_1 = s_1 t_1 s_2 t_2`.
The landed walk (`PocketWalk.exists_of_exteriorAt`) takes the outer sides of two exterior regions `x`, `y`
of one cell to one section and runs `t_2` from the start of `x`'s target arc to the end of `y`'s.  At a
section spanning the whole boundary that arc can be all of `∂Δ`
(`Estimating/OsinPocketWholeSectionWrapModel.lean`).  The inner pocket between the two regions keeps both
arcs proper (`Estimating/OsinPocketInnerWalkModel.lean`): its sides are the reversed inner sides
`invDarts y.rightSide` and `invDarts x.leftSide`, its source arc is the gap between the two source arcs,
and its target arc runs from the end of `x`'s target arc to the start of `y`'s.

* `PocketFaceSet.ofBoundaryCycleOfNotMem`: a pocket face set from a boundary cycle `s_1 t_1⁻¹ s_2 t_2`, with
  the exterior face and the source cell off the face set as hypotheses, and no positivity of the arcs.
* `PocketWalk.exists_inner_of_le`: the inner data, the gap arc `Gap` of the source cell, spanned with
  the two source arcs by an arc `T`, and the target arc `t_2` from the end of `x`'s target arc to the start
  of `y`'s, with both arcs proper and `t_2` in the positions of the section.
* `PocketWalk.ofInner`: the inner pocket walk, when both inner arcs are nonempty.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides

section Constructor

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **A pocket face set from a boundary cycle, without positivity.**  As `PocketFaceSet.ofBoundaryCycle`,
with the exterior face and the source cell off the face set given as hypotheses in place of nonempty
arcs. -/
noncomputable def PocketFaceSet.ofBoundaryCycleOfNotMem {faces : Finset X.toCombMap.Face}
    (boundary : Surgery.MapCollapse.BoundaryCycle X.toCombMap faces)
    (source kept : Fin X.rCellCount)
    (sourceArc : CyclicArc (cellDarts X source)) (targetArc : CyclicArc (outerDarts X))
    (firstSide secondSide : List X.toCombMap.Dart)
    (hcycle : boundary.cycle =
      firstSide ++ invDarts X sourceArc.darts ++ secondSide ++ targetArc.darts)
    (hout : X.outerFace ∉ faces) (hsrc : (cell X source).face ∉ faces)
    (hkept : (cell X kept).face ∈ faces)
    (hfirst : firstSide.length ≤ eps) (hsecond : secondSide.length ≤ eps)
    (hfirstNorm :
      WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X firstSide)) ≤ eps)
    (hsecondNorm :
      WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X secondSide)) ≤ eps)
    (hlo : lo ≤ targetArc.start.1) (hhi : targetArc.start.1 + targetArc.length ≤ hi) :
    PocketFaceSet D eps X lo hi where
  faces := faces
  outerFace_not_mem := hout
  source := source
  source_not_mem := hsrc
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

/-- The reversed darts of a list have its length. -/
theorem length_invDarts (l : List X.toCombMap.Dart) : (invDarts X l).length = l.length := by
  simp only [invDarts, List.length_map, List.length_reverse]

/-- The reversed darts of a list have a value of the same word norm. -/
theorem wordNorm_invDarts (l : List X.toCombMap.Dart) :
    WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X (invDarts X l))) =
      WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X l)) := by
  rw [listVal_dartWord_invDarts, WordMetric.wordNorm_inv D.alphabet.symmetricGenerating]

end Constructor

section Walk

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W} {lambda c : ℝ}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The inner pocket data of two exterior regions.**  Two distinct exterior regions `x`, `y` of the cell
`i` to section `j`, ordered by the start of their target arcs, give a gap arc `Gap` of `Π_i`, spanned with
their source arcs by an arc `T`, and an arc `t_2` of `∂Δ` from the end of `x`'s target arc to the start of
`y`'s, in the positions of section `j`.  Both arcs are proper. -/
theorem PocketWalk.exists_inner_of_le (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {j : Fin cuts.count} {x y : RegionCandidate D eps S.diagram}
    (hx : x ∈ RegionCandidate.exteriorAt S.family i)
    (hy : y ∈ RegionCandidate.exteriorAt S.family i) (hxy : x ≠ y)
    (hjx : RegionCandidate.TargetsSectionIndex cuts j x)
    (hjy : RegionCandidate.TargetsSectionIndex cuts j y)
    (hle : x.2.targetArc.start.1 ≤ y.2.targetArc.start.1) :
    ∃ (Gap T : CyclicArc (cellDarts S.diagram i)) (t₂ : CyclicArc (outerDarts S.diagram)),
      T.darts = x.2.sourceArc.darts ++ Gap.darts ++ y.2.sourceArc.darts ∧
        Gap.length < (cellDarts S.diagram i).length ∧
        t₂.start.1 = x.2.targetArc.start.1 + x.2.targetArc.length ∧
        t₂.start.1 + t₂.length = y.2.targetArc.start.1 ∧
        t₂.length < (outerDarts S.diagram).length ∧
        cuts.cut j.castSucc ≤ t₂.start.1 ∧ t₂.start.1 + t₂.length ≤ cuts.cut j.succ := by
  obtain ⟨hxK, hxi⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyK, hyi⟩ := Finset.mem_filter.mp hy
  have hxS : x ∈ S.family := (Finset.mem_filter.mp hxK).1
  have hyS : y ∈ S.family := (Finset.mem_filter.mp hyK).1
  obtain ⟨hxsrc, hxtgt⟩ := S.nondegenerate x hxS
  obtain ⟨hysrc, -⟩ := S.nondegenerate y hyS
  have hend := RealizedSectionFamily.targetArc_end_le_start S hxS hyS hxy hjx hjy hle
  obtain ⟨htx, hxlo, hxhi⟩ := hjx
  obtain ⟨hty, -, hyhi⟩ := hjy
  obtain ⟨X, -, hXl, hXd⟩ := CyclicArc.exists_transport (cellDarts S.diagram) hxi x.2.sourceArc
  obtain ⟨Y, -, hYl, hYd⟩ := CyclicArc.exists_transport (cellDarts S.diagram) hyi y.2.sourceArc
  have hXY : ∀ d ∈ X.darts, d ∉ Y.darts := by
    intro d hdX hdY
    rw [hXd] at hdX
    rw [hYd] at hdY
    exact Finset.disjoint_left.mp (S.pairwise x hxS y hyS hxy)
      (x.2.faceOf_alpha_mem_of_mem_sourceArc d hdX) (y.2.faceOf_alpha_mem_of_mem_sourceArc d hdY)
  obtain ⟨Gap, T, -, -, hT⟩ := CyclicArc.exists_spanArc X Y (by rw [hXl]; exact hxsrc) hXY
  have hTlen : T.length = X.length + Gap.length + Y.length := by
    have h := congrArg List.length hT
    simp only [List.length_append, T.darts_length, X.darts_length, Gap.darts_length,
      Y.darts_length] at h
    exact h
  have hTle := T.length_le
  rw [hXd, hYd] at hT
  have hn := cut_le_length_outerDarts S j.succ
  obtain ⟨t₂, ht₂s, ht₂l⟩ : ∃ t₂ : CyclicArc (outerDarts S.diagram),
      t₂.start.1 = x.2.targetArc.start.1 + x.2.targetArc.length ∧
        t₂.length = y.2.targetArc.start.1 - (x.2.targetArc.start.1 + x.2.targetArc.length) :=
    ⟨⟨⟨x.2.targetArc.start.1 + x.2.targetArc.length, by omega⟩,
      y.2.targetArc.start.1 - (x.2.targetArc.start.1 + x.2.targetArc.length), by omega⟩, rfl, rfl⟩
  exact ⟨Gap, T, t₂, hT, by omega, ht₂s, by omega, by omega, by omega, by omega⟩

/-- **The inner pocket walk**, when both inner arcs are nonempty: the reversed inner side of `y`, the gap
read backwards, the reversed inner side of `x`, and the arc of `∂Δ` between the two target arcs. -/
noncomputable def PocketWalk.ofInner {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ} (i : Fin X.rCellCount)
    (x y : RegionCandidate D eps X) (Gap : CyclicArc (cellDarts X i)) (t₂ : CyclicArc (outerDarts X))
    (hGap : 0 < Gap.length) (ht₂ : 0 < t₂.length) (hlo : lo ≤ t₂.start.1)
    (hhi : t₂.start.1 + t₂.length ≤ hi) : PocketWalk D eps X lo hi where
  source := i
  sourceArc := Gap
  targetArc := t₂
  firstSide := invDarts X y.2.rightSide
  secondSide := invDarts X x.2.leftSide
  sourceArc_pos := hGap
  targetArc_pos := ht₂
  firstSide_length_le := by rw [length_invDarts]; exact y.2.rightSide_length_le
  secondSide_length_le := by rw [length_invDarts]; exact x.2.leftSide_length_le
  firstSide_norm_le := by rw [wordNorm_invDarts]; exact y.2.rightSide_norm_le
  secondSide_norm_le := by rw [wordNorm_invDarts]; exact x.2.leftSide_norm_le
  lo_le := hlo
  le_hi := hhi

theorem PocketWalk.ofInner_walk {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ} (i : Fin X.rCellCount)
    (x y : RegionCandidate D eps X) (Gap : CyclicArc (cellDarts X i)) (t₂ : CyclicArc (outerDarts X))
    (hGap : 0 < Gap.length) (ht₂ : 0 < t₂.length) (hlo : lo ≤ t₂.start.1)
    (hhi : t₂.start.1 + t₂.length ≤ hi) :
    (PocketWalk.ofInner (lo := lo) (hi := hi) i x y Gap t₂ hGap ht₂ hlo hhi).walk =
      invDarts X y.2.rightSide ++ invDarts X Gap.darts ++ invDarts X x.2.leftSide ++ t₂.darts :=
  rfl

end Walk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalk.exists_inner_of_le
#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalk.ofInner
