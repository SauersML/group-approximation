import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketSectionFaceSet
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionInduction
import GroupApproximation.Meta.AxiomGuard

/-!
# The pocket walk of two regions joining the same two cells

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): two distinct selected regions joining the
same two distinct cells `Π_i` and `Π_j` bound a subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`, where `s_1`, `s_2` are sides of the two regions and `t_1`, `t_2` are
arcs of `Π_i` and `Π_j`.

This module builds the walk data `s_1 t_1 s_2 t_2`, the cell-to-cell analog of
`PocketWalk.exists_of_exteriorAt`, towards `MultipleEdgePocketRegionInput`.

* `RegionCandidate.cellArcList` and `RegionCandidate.sideFrom`: the darts of a region's arc on a
  cell, and the side of the region leaving that cell along its boundary.
* `RegionCandidate.boundary_cycle_rotate_of_joinsCells`: the boundary cycle of a region joining
  the distinct cells `i` and `j` rotates to its arc of `Π_i` read backwards, its side leaving
  `Π_i`, its arc of `Π_j` read backwards and its side leaving `Π_j`, in either direction of the
  region.
* `CellPocketWalk`: nonempty arcs of `Π_i` and `Π_j` and two sides of length and word norm at most
  `ε`.  `CellPocketWalk.walk` is `s_1 ++ invDarts t_1 ++ s_2 ++ invDarts t_2`, the split of
  `MultipleEdgePocketRegionInput`.
* `CellPocketWalk.exists_of_joinsCells`: two distinct selected regions `a`, `b` joining `i` and
  `j` give a walk whose first side is the side of `b` leaving `Π_j`, whose arc of `Π_i` spans the
  arc of `a`, a gap and the arc of `b`, whose second side is the side of `a` leaving `Π_i`, and
  whose arc of `Π_j` spans the arc of `b`, a gap and the arc of `a`.  This is the boundary of `a`,
  the pocket and `b`.  The pair is ordered: `(a, b)` and `(b, a)` give the walks of the two
  complementary pockets of the ring `Π_i`, `a`, `Π_j`, `b`.

Not proved here: that the walk is noncrossing, which of the two pockets avoids the exterior face,
and the pocket region.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, through Osin's Lemma 9.7); certifies no printed sentence
on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded HullSC WordMetric

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ}

/-- A relator-cell target arc on the boundary of a region is the arc read backwards. -/
theorem Embedded.targetBoundaryDarts_eq_invDarts {X : DiscDiagram.{u, w, v} W}
    {target : Option (Fin X.rCellCount)} {arc : CyclicArc (targetDarts X target)}
    {t : Fin X.rCellCount} (h : target = some t) :
    targetBoundaryDarts X target arc = invDarts X arc.darts := by
  subst h
  rfl

namespace Embedded.RegionCandidate

variable {X : DiscDiagram.{u, w, v} W}

/-- The darts of a region's arc on the cell `k`: its source arc when `k` is the source, and its
target arc otherwise. -/
def cellArcList (a : RegionCandidate D eps X) (k : Fin X.rCellCount) : List X.toCombMap.Dart :=
  if a.2.source = k then a.2.sourceArc.darts else a.2.targetArc.darts

/-- The side of a region leaving the cell `k` along its boundary: its right side when `k` is the
source, and its left side otherwise. -/
def sideFrom (a : RegionCandidate D eps X) (k : Fin X.rCellCount) : List X.toCombMap.Dart :=
  if a.2.source = k then a.2.rightSide else a.2.leftSide

theorem sideFrom_length_le (a : RegionCandidate D eps X) (k : Fin X.rCellCount) :
    (a.sideFrom k).length ≤ eps := by
  by_cases hs : a.2.source = k
  · rw [sideFrom, if_pos hs]
    exact a.2.rightSide_length_le
  · rw [sideFrom, if_neg hs]
    exact a.2.leftSide_length_le

theorem sideFrom_norm_le (a : RegionCandidate D eps X) (k : Fin X.rCellCount) :
    wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X (a.sideFrom k))) ≤ eps := by
  by_cases hs : a.2.source = k
  · rw [sideFrom, if_pos hs]
    exact a.2.rightSide_norm_le
  · rw [sideFrom, if_neg hs]
    exact a.2.leftSide_norm_le

/-- A region joining `i` and `j` has `i` as its source or as its target. -/
theorem JoinsCells.source_or_target_left {a : RegionCandidate D eps X} {i j : Fin X.rCellCount}
    (h : a.JoinsCells i j) : a.2.source = i ∨ a.2.target = some i := by
  rcases h with ⟨hs, -⟩ | ⟨-, ht⟩
  · exact Or.inl hs
  · exact Or.inr ht

/-- A region joining `i` and `j` has `j` as its source or as its target. -/
theorem JoinsCells.source_or_target_right {a : RegionCandidate D eps X} {i j : Fin X.rCellCount}
    (h : a.JoinsCells i j) : a.2.source = j ∨ a.2.target = some j := by
  rcases h with ⟨-, ht⟩ | ⟨hs, -⟩
  · exact Or.inr ht
  · exact Or.inl hs

/-- The arc of a region on a cell that is its source or its target is a cyclic arc of that
cell. -/
theorem exists_cellArc (a : RegionCandidate D eps X) {k : Fin X.rCellCount}
    (hk : a.2.source = k ∨ a.2.target = some k) :
    ∃ A : CyclicArc (cellDarts X k), A.darts = a.cellArcList k := by
  by_cases hs : a.2.source = k
  · obtain ⟨A, -, -, hA⟩ := CyclicArc.exists_transport (cellDarts X) hs a.2.sourceArc
    exact ⟨A, hA.trans (by rw [cellArcList, if_pos hs])⟩
  · obtain ⟨A, -, -, hA⟩ :=
      CyclicArc.exists_transport (targetDarts X) (hk.resolve_left hs) a.2.targetArc
    exact ⟨A, hA.trans (by rw [cellArcList, if_neg hs])⟩

/-- With both contiguity arcs nonempty, the arc of a region on any cell is nonempty. -/
theorem cellArcList_length_pos {a : RegionCandidate D eps X}
    (hpos : 0 < a.2.sourceArc.length ∧ 0 < a.2.targetArc.length) (k : Fin X.rCellCount) :
    0 < (a.cellArcList k).length := by
  by_cases hs : a.2.source = k
  · rw [cellArcList, if_pos hs, CyclicArc.darts_length]
    exact hpos.1
  · rw [cellArcList, if_neg hs, CyclicArc.darts_length]
    exact hpos.2

/-- A dart of the arc of a region joining two cells is crossed by `alpha` into the region. -/
theorem faceOf_alpha_mem_of_mem_cellArcList {a : RegionCandidate D eps X}
    {i j k : Fin X.rCellCount} (h : a.JoinsCells i j) {d : X.toCombMap.Dart}
    (hd : d ∈ a.cellArcList k) : X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ a.1 := by
  by_cases hs : a.2.source = k
  · rw [cellArcList, if_pos hs] at hd
    exact a.2.faceOf_alpha_mem_of_mem_sourceArc d hd
  · rw [cellArcList, if_neg hs] at hd
    obtain ⟨t, ht⟩ : ∃ t, a.2.target = some t := by
      rcases h with ⟨-, ht⟩ | ⟨-, ht⟩
      · exact ⟨j, ht⟩
      · exact ⟨i, ht⟩
    exact a.2.faceOf_alpha_mem_of_mem_targetArc t ht d hd

/-- The boundary cycle of a region with a relator-cell target, with both arcs read backwards. -/
theorem boundary_cycle_eq_of_target_eq_some {a : RegionCandidate D eps X} {t : Fin X.rCellCount}
    (ht : a.2.target = some t) :
    a.2.boundary.cycle = invDarts X a.2.sourceArc.darts ++ a.2.rightSide ++
      invDarts X a.2.targetArc.darts ++ a.2.leftSide := by
  rw [a.2.boundary_decomposition, targetBoundaryDarts_eq_invDarts ht]
  rfl

/-- **The boundary of a region joining two cells, read from `Π_i`.**  The boundary cycle of a
region joining the distinct cells `i` and `j` rotates to its arc of `Π_i` read backwards, its side
leaving `Π_i`, its arc of `Π_j` read backwards and its side leaving `Π_j`. -/
theorem boundary_cycle_rotate_of_joinsCells {a : RegionCandidate D eps X}
    {i j : Fin X.rCellCount} (hij : i ≠ j) (h : a.JoinsCells i j) :
    ∃ n : ℕ, a.2.boundary.cycle.rotate n =
      invDarts X (a.cellArcList i) ++ a.sideFrom i ++ invDarts X (a.cellArcList j) ++
        a.sideFrom j := by
  rcases h with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · have hj : ¬a.2.source = j := fun h' => hij (hs.symm.trans h')
    refine ⟨0, ?_⟩
    simp only [List.rotate_zero, boundary_cycle_eq_of_target_eq_some ht, cellArcList, sideFrom,
      if_pos hs, if_neg hj]
  · have hi : ¬a.2.source = i := fun h' => hij (h'.symm.trans hs)
    refine ⟨(invDarts X a.2.sourceArc.darts ++ a.2.rightSide).length, ?_⟩
    simp only [boundary_cycle_eq_of_target_eq_some ht, cellArcList, sideFrom, if_pos hs,
      if_neg hi]
    rw [List.append_assoc (invDarts X a.2.sourceArc.darts ++ a.2.rightSide),
      List.rotate_append_length_eq]
    simp only [List.append_assoc]

end Embedded.RegionCandidate

/-- **A pocket walk between two cells.**  The data of the walk `s_1 t_1 s_2 t_2` of Osin's proof
of Lemma 9.7(b): a nonempty arc `t_1` of `Π_i` and a nonempty arc `t_2` of `Π_j`, both read
backwards, and sides `s_1`, `s_2` of length and word norm at most `ε`. -/
structure CellPocketWalk (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    (i j : Fin X.rCellCount) where
  firstArc : CyclicArc (cellDarts X i)
  secondArc : CyclicArc (cellDarts X j)
  firstSide : List X.toCombMap.Dart
  secondSide : List X.toCombMap.Dart
  firstArc_pos : 0 < firstArc.length
  secondArc_pos : 0 < secondArc.length
  firstSide_length_le : firstSide.length ≤ eps
  secondSide_length_le : secondSide.length ≤ eps
  firstSide_norm_le :
    wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X firstSide)) ≤ eps
  secondSide_norm_le :
    wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X secondSide)) ≤ eps

namespace CellPocketWalk

/-- The walk `s_1 ++ invDarts t_1 ++ s_2 ++ invDarts t_2`. -/
def walk {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}
    (K : CellPocketWalk D eps X i j) : List X.toCombMap.Dart :=
  K.firstSide ++ invDarts X K.firstArc.darts ++ K.secondSide ++ invDarts X K.secondArc.darts

variable {Delta : DiscDiagram.{u, w, v} W} {lambda c : ℝ}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The pocket walk of two regions joining the same two cells.**  Two distinct selected
regions `a`, `b` joining the cells `i` and `j` give a pocket walk: the side of `b` leaving `Π_j`,
the arc of `Π_i` spanning the arc of `a`, a gap and the arc of `b`, read backwards, the side of `a`
leaving `Π_i`, and the arc of `Π_j` spanning the arc of `b`, a gap and the arc of `a`, read
backwards. -/
theorem exists_of_joinsCells (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {i j : Fin S.diagram.rCellCount} {a b : RegionCandidate D eps S.diagram}
    (ha : a ∈ S.family) (hb : b ∈ S.family) (hab : a ≠ b)
    (hai : a.JoinsCells i j) (hbi : b.JoinsCells i j) :
    ∃ K : CellPocketWalk D eps S.diagram i j,
      K.firstSide = b.sideFrom j ∧ K.secondSide = a.sideFrom i ∧
        (∃ G₁ : CyclicArc (cellDarts S.diagram i),
          K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i) ∧
        (∃ G₂ : CyclicArc (cellDarts S.diagram j),
          K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) := by
  have hdisj : Disjoint a.1 b.1 := S.pairwise a ha b hb hab
  obtain ⟨Ai, hAi⟩ := RegionCandidate.exists_cellArc a hai.source_or_target_left
  obtain ⟨Bi, hBi⟩ := RegionCandidate.exists_cellArc b hbi.source_or_target_left
  obtain ⟨Aj, hAj⟩ := RegionCandidate.exists_cellArc a hai.source_or_target_right
  obtain ⟨Bj, hBj⟩ := RegionCandidate.exists_cellArc b hbi.source_or_target_right
  have hai_pos := RegionCandidate.cellArcList_length_pos (S.nondegenerate a ha) i
  have hbj_pos := RegionCandidate.cellArcList_length_pos (S.nondegenerate b hb) j
  have hAiB : ∀ d ∈ Ai.darts, d ∉ Bi.darts := by
    intro d hdA hdB
    rw [hAi] at hdA
    rw [hBi] at hdB
    exact Finset.disjoint_left.mp hdisj
      (RegionCandidate.faceOf_alpha_mem_of_mem_cellArcList hai hdA)
      (RegionCandidate.faceOf_alpha_mem_of_mem_cellArcList hbi hdB)
  have hBjA : ∀ d ∈ Bj.darts, d ∉ Aj.darts := by
    intro d hdB hdA
    rw [hBj] at hdB
    rw [hAj] at hdA
    exact Finset.disjoint_left.mp hdisj
      (RegionCandidate.faceOf_alpha_mem_of_mem_cellArcList hai hdA)
      (RegionCandidate.faceOf_alpha_mem_of_mem_cellArcList hbi hdB)
  obtain ⟨G₁, T₁, -, -, hT₁⟩ :=
    CyclicArc.exists_spanArc Ai Bi (by rw [← Ai.darts_length, hAi]; exact hai_pos) hAiB
  obtain ⟨G₂, T₂, -, -, hT₂⟩ :=
    CyclicArc.exists_spanArc Bj Aj (by rw [← Bj.darts_length, hBj]; exact hbj_pos) hBjA
  rw [hAi, hBi] at hT₁
  rw [hBj, hAj] at hT₂
  have hT₁l : 0 < T₁.length := by
    have h := congrArg List.length hT₁
    simp only [List.length_append, T₁.darts_length] at h
    omega
  have hT₂l : 0 < T₂.length := by
    have h := congrArg List.length hT₂
    simp only [List.length_append, T₂.darts_length] at h
    omega
  exact ⟨
    { firstArc := T₁
      secondArc := T₂
      firstSide := b.sideFrom j
      secondSide := a.sideFrom i
      firstArc_pos := hT₁l
      secondArc_pos := hT₂l
      firstSide_length_le := b.sideFrom_length_le j
      secondSide_length_le := a.sideFrom_length_le i
      firstSide_norm_le := b.sideFrom_norm_le j
      secondSide_norm_le := a.sideFrom_norm_le i },
    rfl, rfl, ⟨G₁, hT₁⟩, ⟨G₂, hT₂⟩⟩

end CellPocketWalk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.targetBoundaryDarts_eq_invDarts
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.boundary_cycle_rotate_of_joinsCells
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.faceOf_alpha_mem_of_mem_cellArcList
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalk.exists_of_joinsCells
