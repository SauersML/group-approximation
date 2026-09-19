import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketSectionFaceSet
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerCornerTwoGonCount
import GroupApproximation.GGT.VanKampen.FaceShellingValue
import GroupApproximation.Meta.AxiomGuard

/-!
# The exclusive pocket walk of two exterior regions

Osin, arXiv:math/0411039v3, Appendix, proof of Lemma 9.7(b): the subdiagram `Γ¹` with
`∂Γ¹ = s₁ t₁ s₂ t₂`.  Route `research/nm-exclusive-pocket-first-turns.md`.

The landed producer `PocketWalk.exists_of_exteriorAt` takes the pocket that contains the two
regions `x`, `y`: its sides are the outer sides `y.leftSide`, `x.rightSide`, its arc `t₁` spans
the source arcs of `x` and `y`, and its arc `t₂` spans their target arcs.  This module takes the
pocket strictly between them:

* `s₁` is the inner side `y.rightSide`, read backwards on reversed darts;
* `t₁` is the gap arc of `∂Π` between the source arcs of `x` and `y`, read backwards;
* `s₂` is the inner side `x.leftSide`, read backwards on reversed darts;
* `t₂` is the stretch of `∂Δ` from the end of `x`'s target arc to the start of `y`'s.

The arcs may be empty, so the data is `ExclusiveWalk`, which is `PocketWalk` without the two
positivity fields.  The turns of this walk are first turns (`Estimating/OsinPocketExclusiveTurns`).

* `ExclusiveWalk`, `ExclusiveWalk.walk`.
* `ExclusiveWalk.length_invDarts`, `ExclusiveWalk.norm_invDarts_le`: an inner side read backwards
  keeps the side bounds.
* `ExclusiveWalk.targetArc_end_le_start`: two distinct exterior regions of one cell to one
  section, the first starting no later, have disjoint target arcs, the first ending before the
  second starts.
* `ExclusiveWalk.exists_of_le`, `ExclusiveWalk.exists_of_exteriorAt`: the exclusive walk data.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded HullSC WordMetric

section Walk

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **The exclusive pocket walk data**: an arc `t₁` of the cell `source`, an arc `t₂` of `∂X`
between the positions `lo` and `hi`, and two sides no longer than `ε` with values no longer than
`ε`.  Unlike `PocketWalk`, the arcs may be empty. -/
structure ExclusiveWalk (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    (lo hi : ℕ) where
  source : Fin X.rCellCount
  sourceArc : CyclicArc (cellDarts X source)
  targetArc : CyclicArc (outerDarts X)
  firstSide : List X.toCombMap.Dart
  secondSide : List X.toCombMap.Dart
  firstSide_length_le : firstSide.length ≤ eps
  secondSide_length_le : secondSide.length ≤ eps
  firstSide_norm_le :
    wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X firstSide)) ≤ eps
  secondSide_norm_le :
    wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X secondSide)) ≤ eps
  lo_le : lo ≤ targetArc.start.1
  le_hi : targetArc.start.1 + targetArc.length ≤ hi

namespace ExclusiveWalk

variable {D : RelGenSet G Lambda} {eps : ℕ}

/-- The walk `s₁ t₁ s₂ t₂`, with `t₁` read backwards. -/
def walk {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ} (K : ExclusiveWalk D eps X lo hi) :
    List X.toCombMap.Dart :=
  K.firstSide ++ invDarts X K.sourceArc.darts ++ K.secondSide ++ K.targetArc.darts

/-- Reading a list backwards on reversed darts keeps its length. -/
theorem length_invDarts (X : DiscDiagram.{u, w, v} W) (l : List X.toCombMap.Dart) :
    (invDarts X l).length = l.length := by
  simp only [invDarts, List.length_map, List.length_reverse]

/-- Reading a side backwards on reversed darts keeps its norm bound: the value is inverted. -/
theorem norm_invDarts_le {X : DiscDiagram.{u, w, v} W} {l : List X.toCombMap.Dart}
    (h : wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X l)) ≤ eps) :
    wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X (invDarts X l))) ≤ eps := by
  rw [listVal_dartWord_invDarts, wordNorm_inv D.alphabet.symmetricGenerating]
  exact h

variable {Delta : DiscDiagram.{u, w, v} W} {lambda c : ℝ}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **Disjoint ordered target arcs.**  Two distinct exterior regions of the cell `i` to section
`j`, the target arc of `x` starting no later than that of `y`, have the target arc of `x` ending
before that of `y` starts: otherwise the dart of `∂Δ` at the start of `y`'s target arc lies on
the boundary of both regions, and they share a face. -/
theorem targetArc_end_le_start (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {j : Fin cuts.count} {x y : RegionCandidate D eps S.diagram}
    (hx : x ∈ RegionCandidate.exteriorAt S.family i)
    (hy : y ∈ RegionCandidate.exteriorAt S.family i) (hxy : x ≠ y)
    (hjx : RegionCandidate.TargetsSectionIndex cuts j x)
    (hjy : RegionCandidate.TargetsSectionIndex cuts j y)
    (hle : x.2.targetArc.start.1 ≤ y.2.targetArc.start.1) :
    x.2.targetArc.start.1 + x.2.targetArc.length ≤ y.2.targetArc.start.1 := by
  obtain ⟨hxK, -⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyK, -⟩ := Finset.mem_filter.mp hy
  have hxS : x ∈ S.family := (Finset.mem_filter.mp hxK).1
  have hyS : y ∈ S.family := (Finset.mem_filter.mp hyK).1
  obtain ⟨-, hytgt⟩ := S.nondegenerate y hyS
  obtain ⟨hxt, -, hxhi⟩ := hjx
  obtain ⟨hyt, -, hyhi⟩ := hjy
  have hn := PocketWalk.cut_le_length_outerDarts S j.succ
  by_contra hlt
  have hp : y.2.targetArc.start.1 < (outerDarts S.diagram).length := by omega
  have hma := getElem_outerDarts_mem_targetBoundaryDarts S.diagram x.2.target x.2.targetArc hxt
    (p := y.2.targetArc.start.1) hle (by omega) (by omega)
  have hmb := getElem_outerDarts_mem_targetBoundaryDarts S.diagram y.2.target y.2.targetArc hyt
    (p := y.2.targetArc.start.1) le_rfl (by omega) (by omega)
  have hca : (outerDarts S.diagram)[y.2.targetArc.start.1]'hp ∈ x.2.boundary.cycle := by
    rw [x.2.boundary_decomposition]
    exact List.mem_append_left _ (List.mem_append_right _ hma)
  have hcb : (outerDarts S.diagram)[y.2.targetArc.start.1]'hp ∈ y.2.boundary.cycle := by
    rw [y.2.boundary_decomposition]
    exact List.mem_append_left _ (List.mem_append_right _ hmb)
  exact hxy (RegionCandidate.eq_of_face_mem_of_face_mem S.pairwise hxS hyS
    ((x.2.boundary.cycle_mem_iff _).mp hca).1 ((y.2.boundary.cycle_mem_iff _).mp hcb).1)

/-- **The exclusive walk of two ordered exterior regions.**  Two distinct exterior regions `x`,
`y` of the cell `i` to section `j`, with the target arc of `x` starting no later than that of
`y`, give exclusive walk data in the positions of section `j`: `y`'s right side and `x`'s left
side read backwards on reversed darts, the gap arc of `Π_i` between the source arcs of `x` and
`y`, and the stretch of `∂Δ` from the end of `x`'s target arc to the start of `y`'s. -/
theorem exists_of_le (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {j : Fin cuts.count} {x y : RegionCandidate D eps S.diagram}
    (hx : x ∈ RegionCandidate.exteriorAt S.family i)
    (hy : y ∈ RegionCandidate.exteriorAt S.family i) (hxy : x ≠ y)
    (hjx : RegionCandidate.TargetsSectionIndex cuts j x)
    (hjy : RegionCandidate.TargetsSectionIndex cuts j y)
    (hle : x.2.targetArc.start.1 ≤ y.2.targetArc.start.1) :
    ∃ K : ExclusiveWalk D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ),
      K.source = i ∧ K.firstSide = invDarts S.diagram y.2.rightSide ∧
        K.secondSide = invDarts S.diagram x.2.leftSide ∧
        (∃ X Y T : CyclicArc (cellDarts S.diagram i),
          X.darts = x.2.sourceArc.darts ∧ Y.darts = y.2.sourceArc.darts ∧
            K.sourceArc.start = X.rest.start ∧ T.start = X.start ∧
            T.darts = X.darts ++ K.sourceArc.darts ++ Y.darts) ∧
        K.targetArc.start.1 = x.2.targetArc.start.1 + x.2.targetArc.length ∧
        K.targetArc.start.1 + K.targetArc.length = y.2.targetArc.start.1 := by
  have hord := targetArc_end_le_start S hx hy hxy hjx hjy hle
  obtain ⟨hxK, hxi⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyK, hyi⟩ := Finset.mem_filter.mp hy
  have hxS : x ∈ S.family := (Finset.mem_filter.mp hxK).1
  have hyS : y ∈ S.family := (Finset.mem_filter.mp hyK).1
  obtain ⟨hxsrc, -⟩ := S.nondegenerate x hxS
  obtain ⟨-, hytgt⟩ := S.nondegenerate y hyS
  obtain ⟨-, hxlo, -⟩ := hjx
  obtain ⟨-, -, hyhi⟩ := hjy
  obtain ⟨X, -, hXl, hXd⟩ := CyclicArc.exists_transport (cellDarts S.diagram) hxi x.2.sourceArc
  obtain ⟨Y, -, -, hYd⟩ := CyclicArc.exists_transport (cellDarts S.diagram) hyi y.2.sourceArc
  have hXY : ∀ d ∈ X.darts, d ∉ Y.darts := by
    intro d hdX hdY
    rw [hXd] at hdX
    rw [hYd] at hdY
    exact Finset.disjoint_left.mp (S.pairwise x hxS y hyS hxy)
      (x.2.faceOf_alpha_mem_of_mem_sourceArc d hdX) (y.2.faceOf_alpha_mem_of_mem_sourceArc d hdY)
  obtain ⟨Gap, T, hGs, hTs, hT⟩ :=
    CyclicArc.exists_spanArc X Y (by rw [hXl]; exact hxsrc) hXY
  have hn := PocketWalk.cut_le_length_outerDarts S j.succ
  obtain ⟨t₂, ht₂s, ht₂l⟩ : ∃ t₂ : CyclicArc (outerDarts S.diagram),
      t₂.start.1 = x.2.targetArc.start.1 + x.2.targetArc.length ∧
        t₂.length = y.2.targetArc.start.1 - (x.2.targetArc.start.1 + x.2.targetArc.length) :=
    ⟨⟨⟨x.2.targetArc.start.1 + x.2.targetArc.length, by omega⟩,
      y.2.targetArc.start.1 - (x.2.targetArc.start.1 + x.2.targetArc.length), by omega⟩, rfl, rfl⟩
  have hend : t₂.start.1 + t₂.length = y.2.targetArc.start.1 := by omega
  refine ⟨
    { source := i
      sourceArc := Gap
      targetArc := t₂
      firstSide := invDarts S.diagram y.2.rightSide
      secondSide := invDarts S.diagram x.2.leftSide
      firstSide_length_le := by
        rw [length_invDarts]
        exact y.2.rightSide_length_le
      secondSide_length_le := by
        rw [length_invDarts]
        exact x.2.leftSide_length_le
      firstSide_norm_le := norm_invDarts_le y.2.rightSide_norm_le
      secondSide_norm_le := norm_invDarts_le x.2.leftSide_norm_le
      lo_le := by omega
      le_hi := by omega }, rfl, rfl, rfl, ⟨X, Y, T, hXd, hYd, hGs, hTs, hT⟩, ht₂s, hend⟩

/-- **The exclusive walk of two exterior regions.**  Two distinct exterior regions of the cell
`i` to section `j`, ordered as `x`, `y` by the start of their target arcs, give exclusive walk
data in the positions of section `j` (`exists_of_le`). -/
theorem exists_of_exteriorAt (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {j : Fin cuts.count} {a b : RegionCandidate D eps S.diagram}
    (ha : a ∈ RegionCandidate.exteriorAt S.family i)
    (hb : b ∈ RegionCandidate.exteriorAt S.family i) (hab : a ≠ b)
    (hja : RegionCandidate.TargetsSectionIndex cuts j a)
    (hjb : RegionCandidate.TargetsSectionIndex cuts j b) :
    ∃ (K : ExclusiveWalk D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ))
      (x y : RegionCandidate D eps S.diagram), (x = a ∧ y = b ∨ x = b ∧ y = a) ∧
      K.source = i ∧ K.firstSide = invDarts S.diagram y.2.rightSide ∧
        K.secondSide = invDarts S.diagram x.2.leftSide ∧
        (∃ X Y T : CyclicArc (cellDarts S.diagram i),
          X.darts = x.2.sourceArc.darts ∧ Y.darts = y.2.sourceArc.darts ∧
            K.sourceArc.start = X.rest.start ∧ T.start = X.start ∧
            T.darts = X.darts ++ K.sourceArc.darts ++ Y.darts) ∧
        K.targetArc.start.1 = x.2.targetArc.start.1 + x.2.targetArc.length ∧
        K.targetArc.start.1 + K.targetArc.length = y.2.targetArc.start.1 := by
  by_cases hle : a.2.targetArc.start.1 ≤ b.2.targetArc.start.1
  · obtain ⟨K, hK⟩ := exists_of_le S ha hb hab hja hjb hle
    exact ⟨K, a, b, Or.inl ⟨rfl, rfl⟩, hK⟩
  · obtain ⟨K, hK⟩ := exists_of_le S hb ha (Ne.symm hab) hjb hja (by omega)
    exact ⟨K, b, a, Or.inr ⟨rfl, rfl⟩, hK⟩

end ExclusiveWalk

end Walk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveWalk.norm_invDarts_le
#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveWalk.targetArc_end_le_start
#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveWalk.exists_of_le
#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveWalk.exists_of_exteriorAt
