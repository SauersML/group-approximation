import GroupApproximation.GGT.VanKampen.SurgeryCellSideThickening
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCopyWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionCounting
import GroupApproximation.Meta.AxiomGuard

/-!
# The side condition of the pocket walk on a cell-side-free copy

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`, where `s_1, s_2` are side arcs of contiguity subdiagrams of the
cell `Π`.

The edge conditions `PocketWalk.CopyClean` (`Estimating/OsinPocketCopyWalk.lean`) include
`side_cell`: no dart of the left side of `y` or of the right side of `x` has the source cell `Π`
across it.  This module proves that field for two distinct exterior regions of one cell, on a
least-area diagram with no cell-side dart (`CellSideThickening.IsCellSideDart`), which is the
output of `CellSideThickening.cellSideThickening`.

* When `Π` has at least two darts, a side dart with `Π` across it makes its reverse a cell-side
  dart.  At least area no region contains a relator cell (`ContiguityGeometry.innerGRegion`).
* When `Π` has one dart, that dart lies in the source arc of `x`, which is nonempty.  So a side
  dart with `Π` across it lies in the boundary of `x` read along the source.  On the right side
  of `x` it would occur twice in the boundary cycle of `x`.  On the left side of `y` its face
  would lie in both regions.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.CellSideThickening

open HullSC Embedded
open scoped Classical

universe u w v

/-- Two members of a list with at most one entry are equal. -/
theorem eq_of_mem_of_length_le_one {α : Type*} {l : List α} (hl : l.length ≤ 1) {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) : a = b := by
  rcases l with _ | ⟨e, _ | ⟨e', l⟩⟩
  · exact absurd ha List.not_mem_nil
  · rw [List.mem_singleton] at ha hb
    exact ha.trans hb.symm
  · simp only [List.length_cons] at hl
    omega

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **No side dart of two exterior regions of one cell has that cell across it**, on a
least-area diagram with no cell-side dart.  This is the field `side_cell` of
`PocketWalk.CopyClean` for the pocket walk of `x` and `y` at the cell `i`. -/
theorem side_cell_of_noCellSideDart
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (hfree : ∀ x, ¬ IsCellSideDart S.diagram S.family x) (hlea : S.diagram.LeastArea)
    {i : Fin S.diagram.rCellCount} {x y : RegionCandidate D eps S.diagram}
    (hx : x ∈ RegionCandidate.exteriorAt S.family i)
    (hy : y ∈ RegionCandidate.exteriorAt S.family i) (hxy : x ≠ y) :
    ∀ d ∈ y.2.leftSide ++ x.2.rightSide,
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ≠ (cell S.diagram i).face := by
  intro d hd hface
  simp only [RegionCandidate.exteriorAt, RegionCandidate.ofKind, Finset.mem_filter] at hx hy
  obtain ⟨⟨hxS, -⟩, hxi⟩ := hx
  obtain ⟨⟨hyS, -⟩, -⟩ := hy
  have havoid : ∀ z ∈ S.family, (cell S.diagram i).face ∉ z.1 := fun z _ =>
    (z.2.innerGRegion hlea).cells_avoid (cell S.diagram i) (cell_mem S.diagram i)
  by_cases hlen : 1 < (S.diagram.faceBoundary (cell S.diagram i).face).darts.length
  · apply hfree (S.diagram.toCombMap.alpha d)
    refine ⟨⟨cell S.diagram i, cell_mem S.diagram i, hface⟩, ?_, ?_, ?_⟩
    · rw [hface]
      exact hlen
    · intro z hz
      rw [hface]
      exact havoid z hz
    · rw [S.diagram.toCombMap.alpha_involutive d]
      rcases List.mem_append.mp hd with hl | hr
      · exact ⟨y, hyS, List.mem_append_right _ hl⟩
      · exact ⟨x, hxS, List.mem_append_left _ hr⟩
  · have hlen1 : (S.diagram.faceBoundary (cell S.diagram i).face).darts.length ≤ 1 :=
      Nat.le_of_not_lt hlen
    have hnd := (S.nondegenerate x hxS).1
    have hne : x.2.sourceArc.darts ≠ [] := by
      intro hnil
      have h0 := x.2.sourceArc.darts_length
      rw [hnil, List.length_nil] at h0
      omega
    obtain ⟨e', he'⟩ := List.exists_mem_of_ne_nil _ hne
    have he'face : S.diagram.toCombMap.faceOf e' = (cell S.diagram i).face := by
      have hmem := x.2.sourceArc.mem_cycle_of_mem_darts he'
      rw [← hxi]
      exact ((S.diagram.faceBoundary (cell S.diagram x.2.source).face).mem_iff e').mp hmem
    have hmemA : S.diagram.toCombMap.alpha d ∈
        (S.diagram.faceBoundary (cell S.diagram i).face).darts :=
      ((S.diagram.faceBoundary _).mem_iff _).mpr hface
    have hmemE : e' ∈ (S.diagram.faceBoundary (cell S.diagram i).face).darts :=
      ((S.diagram.faceBoundary _).mem_iff _).mpr he'face
    have heq : e' = S.diagram.toCombMap.alpha d := eq_of_mem_of_length_le_one hlen1 hmemE hmemA
    have hrev : d ∈ x.2.sourceArc.reverseDarts := by
      refine List.mem_map.mpr ⟨S.diagram.toCombMap.alpha d, List.mem_reverse.mpr (heq ▸ he'), ?_⟩
      exact S.diagram.toCombMap.alpha_involutive d
    rcases List.mem_append.mp hd with hl | hr
    · have hcx : d ∈ x.2.boundary.cycle := by
        rw [x.2.boundary_decomposition]
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hrev))
      have hcy : d ∈ y.2.boundary.cycle := by
        rw [y.2.boundary_decomposition]
        exact List.mem_append_right _ hl
      exact Finset.disjoint_left.mp (S.pairwise x hxS y hyS hxy)
        ((x.2.boundary.cycle_mem_iff d).mp hcx).1 ((y.2.boundary.cycle_mem_iff d).mp hcy).1
    · have hnodup := x.2.boundary.cycle_nodup
      rw [x.2.boundary_decomposition] at hnodup
      exact (List.nodup_append.mp (List.nodup_append.mp (List.nodup_append.mp hnodup).1).1).2.2 _
        hrev _ hr rfl

end GroupApproximation.GGT.VanKampen.CellSideThickening

#audit_axioms GroupApproximation.GGT.VanKampen.CellSideThickening.eq_of_mem_of_length_le_one
#audit_axioms GroupApproximation.GGT.VanKampen.CellSideThickening.side_cell_of_noCellSideDart
