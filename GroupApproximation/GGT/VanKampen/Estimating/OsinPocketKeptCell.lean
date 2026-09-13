import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketZeroCellMergeFalse
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketSectionFaceSet
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionSimpleWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerCornerTwoGonCount
import GroupApproximation.Meta.AxiomGuard

/-!
# The kept cell of the pocket between two exterior regions

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(a): "otherwise one can include the
ε-contiguity subdiagrams corresponding to the edges `e` and `f` of `Φ'_M` into a single
ε-contiguity subdiagram in the obvious way, contrary to the definition of `M`."

Two distinct exterior regions `x`, `y` of one cell to one section give the pocket walk
`s_1 t_1 s_2 t_2` (`PocketWalk.exists_of_le`).  If a pocket region with this walk as its cycle
held no relator cell, it would merge `x` and `y` into one contiguity region whose arcs are at least
as long as theirs together, against the choice of the family
(`GloballyDistinguishedSectionFamily.false_of_disc_pair_singleton`).  So a relator cell lies in
the pocket: this is the cell `kept` of `PocketWalk.toPocketFaceSet`.

Everything is stated on the diagram of the family itself.  The O-equivalent copy of
`SectionPocketFaceSetInput` is the diagram of the family `S'` of `OuterSpurThickeningStatement`,
which is again globally distinguished, so nothing is transported along the O-equivalence.  An
O-equivalence matches boundary words and cell words but no darts, so it could not carry the side
of a walk.

* `RealizedSectionFamily.targetArc_end_le_start`: of two distinct regions to one section, the
  target arc starting first ends before the other starts.
* `GloballyDistinguishedSectionFamily.exists_kept_of_pocketRegion`: a pocket region whose cycle is
  the pocket walk holds a relator cell, if every other selected region avoids it.
* `GloballyDistinguishedSectionFamily.exists_kept_of_simple`: for a simple pocket walk, a relator
  cell lies on its side.

Not proved here: that the other selected regions avoid the pocket (`havoid`).  A third region of
the same cell to the same section can lie between `x` and `y`, inside the pocket, and is then
absorbed as well.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, through Osin's Lemma 9.7); certifies no printed sentence
on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}

namespace RealizedSectionFamily

/-- **Ordered target arcs in one section do not overlap.**  Of two distinct selected regions to
section `j`, the target arc of `x`, starting no later than that of `y`, ends before that of `y`
starts. -/
theorem targetArc_end_le_start (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {j : Fin cuts.count} {x y : RegionCandidate D eps S.diagram}
    (hxS : x ∈ S.family) (hyS : y ∈ S.family) (hxy : x ≠ y)
    (hjx : RegionCandidate.TargetsSectionIndex cuts j x)
    (hjy : RegionCandidate.TargetsSectionIndex cuts j y)
    (hle : x.2.targetArc.start.1 ≤ y.2.targetArc.start.1) :
    x.2.targetArc.start.1 + x.2.targetArc.length ≤ y.2.targetArc.start.1 := by
  by_contra hne
  have hlt := not_le.mp hne
  obtain ⟨htx, -, hxhi⟩ := hjx
  obtain ⟨hty, -, hyhi⟩ := hjy
  have hn := PocketWalk.cut_le_length_outerDarts S j.succ
  have hylen := (S.nondegenerate y hyS).2
  have hLx : x.2.targetArc.start.1 + x.2.targetArc.length ≤ (outerDarts S.diagram).length := by
    omega
  have hLy : y.2.targetArc.start.1 + y.2.targetArc.length ≤ (outerDarts S.diagram).length := by
    omega
  have hmx := getElem_outerDarts_mem_targetBoundaryDarts S.diagram x.2.target x.2.targetArc htx
    hle hlt hLx
  have hmy := getElem_outerDarts_mem_targetBoundaryDarts S.diagram y.2.target y.2.targetArc hty
    le_rfl (by omega) hLy
  have hcx : (outerDarts S.diagram)[y.2.targetArc.start.1]'(by omega) ∈ x.2.boundary.cycle := by
    rw [x.2.boundary_decomposition]
    exact List.mem_append_left _ (List.mem_append_right _ hmx)
  have hcy : (outerDarts S.diagram)[y.2.targetArc.start.1]'(by omega) ∈ y.2.boundary.cycle := by
    rw [y.2.boundary_decomposition]
    exact List.mem_append_left _ (List.mem_append_right _ hmy)
  exact Finset.disjoint_left.mp (S.pairwise x hxS y hyS hxy)
    ((x.2.boundary.cycle_mem_iff _).mp hcx).1 ((y.2.boundary.cycle_mem_iff _).mp hcy).1

end RealizedSectionFamily

namespace GloballyDistinguishedSectionFamily

/-- **The kept cell of a pocket region.**  Let `x ≠ y` be exterior regions of the cell `i` to
section `j`, the target arc of `x` starting first, and `K` their pocket walk, as given by
`PocketWalk.exists_of_le`: the source arc of `K` spans those of `x`, a gap and `y`, and its target
arc runs from the start of the target arc of `x` to the end of that of `y`.  Let `P` be a pocket
region whose cycle is the walk, avoided by every other selected region.  Then a relator cell lies
in `P`.  Otherwise `P` merges `x` and `y` into one contiguity region to section `j`, with arcs at
least as long as theirs together. -/
theorem exists_kept_of_pocketRegion
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {j : Fin cuts.count} {x y : RegionCandidate D eps S.diagram}
    (hx : x ∈ RegionCandidate.exteriorAt S.family i)
    (hy : y ∈ RegionCandidate.exteriorAt S.family i) (hxy : x ≠ y)
    (hjx : RegionCandidate.TargetsSectionIndex cuts j x)
    (hjy : RegionCandidate.TargetsSectionIndex cuts j y)
    (hle : x.2.targetArc.start.1 ≤ y.2.targetArc.start.1)
    (K : PocketWalk D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ))
    (hgap : ∃ Gap : CyclicArc (cellDarts S.diagram i),
      K.sourceArc.darts = x.2.sourceArc.darts ++ Gap.darts ++ y.2.sourceArc.darts)
    (hstart : K.targetArc.start.1 = x.2.targetArc.start.1)
    (hend : K.targetArc.start.1 + K.targetArc.length =
      y.2.targetArc.start.1 + y.2.targetArc.length)
    (P : PocketRegion S.diagram) (hinner : P.inner.cycle = K.walk)
    (havoid : ∀ z ∈ S.family, z ≠ x → z ≠ y → Disjoint z.1 P.faces) :
    ∃ kept : Fin S.diagram.rCellCount, (cell S.diagram kept).face ∈ P.faces := by
  by_contra hno
  have hcells : ∀ C ∈ S.diagram.relatorCells, C.face ∉ P.faces := by
    intro C hC hmem
    obtain ⟨n, rfl⟩ := List.mem_iff_get.mp hC
    exact hno ⟨n, hmem⟩
  have hxS : x ∈ S.family := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  have hyS : y ∈ S.family := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).1
  have horder := RealizedSectionFamily.targetArc_end_le_start S.toRealizedSectionFamily hxS hyS
    hxy hjx hjy hle
  obtain ⟨Gap, hGap⟩ := hgap
  have hsrc := congrArg List.length hGap
  simp only [List.length_append, Embedded.CyclicArc.darts_length] at hsrc
  have hrot : (Surgery.InnerDiscRegion.ofPocketRegion P hcells).region.cycle.rotate
      K.firstSide.length = K.sourceArc.reverseDarts ++ K.secondSide ++
        targetBoundaryDarts S.diagram none K.targetArc ++ K.firstSide := by
    rw [Surgery.InnerDiscRegion.ofPocketRegion_region_cycle, hinner]
    show (K.firstSide ++ invDarts S.diagram K.sourceArc.darts ++ K.secondSide ++
        K.targetArc.darts).rotate K.firstSide.length =
      invDarts S.diagram K.sourceArc.darts ++ K.secondSide ++ K.targetArc.darts ++ K.firstSide
    simp only [List.append_assoc, List.rotate_append_length_eq]
  refine S.false_of_disc_pair_singleton hxS hyS hxy
    (Surgery.InnerDiscRegion.ofPocketRegion P hcells) havoid
    ((Surgery.InnerDiscRegion.ofPocketRegion P hcells).mergedGeometry (target := none)
      K.sourceArc K.targetArc hrot K.secondSide_length_le K.firstSide_length_le
      K.secondSide_norm_le K.firstSide_norm_le) ?_ ?_ ?_ ?_
  · rw [Surgery.InnerDiscRegion.mergedGeometry_targetArc_start,
      Surgery.InnerDiscRegion.mergedGeometry_targetArc_length]
    exact fun _ => ⟨j, K.lo_le, K.le_hi⟩
  · rw [Surgery.InnerDiscRegion.mergedGeometry_sourceArc_length]
    exact K.sourceArc_pos
  · rw [Surgery.InnerDiscRegion.mergedGeometry_targetArc_length]
    exact K.targetArc_pos
  · rw [Surgery.InnerDiscRegion.mergedGeometry_sourceArc_length,
      Surgery.InnerDiscRegion.mergedGeometry_targetArc_length]
    simp only [RegionCandidate.weight]
    omega

/-- **The kept cell of a simple pocket walk.**  With `x`, `y` and `K` as in
`exists_kept_of_pocketRegion`, if the pocket walk is a simple closed walk and every other selected
region avoids its side, a relator cell lies on its side.  This is the premise `hkept` of
`PocketWalk.toPocketFaceSet`. -/
theorem exists_kept_of_simple
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {j : Fin cuts.count} {x y : RegionCandidate D eps S.diagram}
    (hx : x ∈ RegionCandidate.exteriorAt S.family i)
    (hy : y ∈ RegionCandidate.exteriorAt S.family i) (hxy : x ≠ y)
    (hjx : RegionCandidate.TargetsSectionIndex cuts j x)
    (hjy : RegionCandidate.TargetsSectionIndex cuts j y)
    (hle : x.2.targetArc.start.1 ≤ y.2.targetArc.start.1)
    (K : PocketWalk D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ))
    (hgap : ∃ Gap : CyclicArc (cellDarts S.diagram i),
      K.sourceArc.darts = x.2.sourceArc.darts ++ Gap.darts ++ y.2.sourceArc.darts)
    (hstart : K.targetArc.start.1 = x.2.targetArc.start.1)
    (hend : K.targetArc.start.1 + K.targetArc.length =
      y.2.targetArc.start.1 + y.2.targetArc.length)
    (hw : IsSimpleClosedWalk S.diagram.toCombMap K.walk)
    (havoid : ∀ z ∈ S.family, z ≠ x → z ≠ y →
      Disjoint z.1 (sideFaces S.diagram.toCombMap K.walk)) :
    ∃ kept : Fin S.diagram.rCellCount,
      (cell S.diagram kept).face ∈ sideFaces S.diagram.toCombMap K.walk := by
  obtain ⟨d, hd⟩ := K.targetArc.exists_mem_darts K.targetArc_pos
  have hdw : d ∈ K.walk := by
    show d ∈ K.firstSide ++ invDarts S.diagram K.sourceArc.darts ++ K.secondSide ++
      K.targetArc.darts
    exact List.mem_append_right _ hd
  have hout := PocketFaceSet.outerFace_not_mem_sideFaces_of_mem_outerDarts hw hdw
    (K.targetArc.mem_cycle_of_mem_darts hd)
  exact S.exists_kept_of_pocketRegion hx hy hxy hjx hjy hle K ⟨Gap, hGap⟩ hstart hend
    (PocketRegion.ofSimpleClosedWalk hw hout) (PocketRegion.ofSimpleClosedWalk_inner_cycle hw hout)
    havoid

end GloballyDistinguishedSectionFamily

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.RealizedSectionFamily.targetArc_end_le_start
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.exists_kept_of_pocketRegion
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.exists_kept_of_simple
