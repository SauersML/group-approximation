import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellMeetsContained
import GroupApproximation.Meta.AxiomGuard

/-!
# The kept relator cell of the pocket between two cells

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): two distinct selected regions joining the
same two distinct cells `Π_i` and `Π_j` bound a subdiagram `Γ_1` with `∂Γ_1 = s_1 t_1 s_2 t_2`
containing both regions.  If `Γ_1` held no relator cell, the regions could be merged into one
contiguity region from `Π_i` to `Π_j`, "contrary to the definition" of the distinguished system.

This module is step 5 of the binder-5 route to `MultipleEdgePocketRegionInput`, the cell-to-cell
analogue of `GloballyDistinguishedSectionFamily.exists_kept_of_pocketRegion_of_value`.

* If no relator word has value one, every selected region meeting a pocket region `P` whose cycle
  is the walk lies in `P` (`RealizedRegionFamily.subset_of_not_disjoint_cellPocketRegion`).
* The arcs of `a` and `b` on `Π_i` lie on `t_1`, so both regions meet `P`.
* If `P` held no relator cell, its collapse would absorb the regions meeting it, at least two.
  Their arc darts lie on `t_1` and `t_2` and are pairwise distinct, so their weights add up to at
  most `|t_1| + |t_2|`.  The merged face reads `t_1`, the side `s_2`, `t_2` and the side `s_1`: a
  contiguity region from `Π_i` to `Π_j ≠ Π_i`, which contradicts the choice of the family
  (`false_of_disc_absorbed_section`).

* `GloballyDistinguishedSectionFamily.exists_kept_of_cellPocketRegion_of_value`: the kept cell.
* `GloballyDistinguishedSectionFamily.exists_kept_of_cellPocketRegion_of_leastArea`: the same at
  least area.
* `CellPocketKeptCellStatement` / `cellPocketKeptCell`: the same for the pocket walk given by
  `CellPocketWalk.exists_of_joinsCells`, proved.

## Manuscript status

Infrastructure for `thm:hull` ("Hull's small cancellation theorem", through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

namespace CellPocketKeptCell

/-- Three disjointness facts of a duplicate-free list `A ++ B ++ C ++ E`. -/
theorem nodup_four {α : Type*} {A B C E : List α} (h : (A ++ B ++ C ++ E).Nodup) :
    (A ++ C).Nodup ∧ (∀ d ∈ A ++ C, d ∉ B) ∧ (∀ d ∈ A ++ C, d ∉ E) := by
  obtain ⟨h3, -, hE⟩ := List.nodup_append.mp h
  obtain ⟨h2, hC, hBC⟩ := List.nodup_append.mp h3
  obtain ⟨hA, -, hAB⟩ := List.nodup_append.mp h2
  refine ⟨List.nodup_append.mpr ⟨hA, hC, fun a ha b hb =>
    hBC a (List.mem_append_left _ ha) b hb⟩, ?_, ?_⟩
  · intro d hd hdB
    rcases List.mem_append.mp hd with hdA | hdC
    · exact hAB d hdA d hdB rfl
    · exact hBC d (List.mem_append_right _ hdB) d hdC rfl
  · intro d hd hdE
    rcases List.mem_append.mp hd with hdA | hdC
    · exact hE d (List.mem_append_left _ (List.mem_append_left _ hdA)) d hdE rfl
    · exact hE d (List.mem_append_right _ hdC) d hdE rfl

/-- A dart of a target arc on the boundary of a region crosses into the exterior or a cell. -/
theorem faceOf_alpha_of_mem_targetBoundaryDarts {X : DiscDiagram.{u, w, v} W}
    {target : Option (Fin X.rCellCount)} (arc : CyclicArc (targetDarts X target))
    {d : X.toCombMap.Dart} (hd : d ∈ targetBoundaryDarts X target arc) :
    X.toCombMap.faceOf (X.toCombMap.alpha d) = X.outerFace ∨
      ∃ k : Fin X.rCellCount, X.toCombMap.faceOf (X.toCombMap.alpha d) = (cell X k).face := by
  cases target with
  | none =>
    left
    have hdo : d ∈ outerDarts X := arc.mem_cycle_of_mem_darts hd
    simp only [outerDarts, List.mem_map, List.mem_reverse] at hdo
    obtain ⟨e, he, rfl⟩ := hdo
    rw [X.toCombMap.alpha_involutive e]
    exact ((X.faceBoundary X.outerFace).mem_iff e).mp he
  | some k =>
    right
    refine ⟨k, ?_⟩
    have hs : d ∈ arc.reverseDarts := hd
    simp only [CyclicArc.reverseDarts, List.mem_map, List.mem_reverse] at hs
    obtain ⟨e, he, rfl⟩ := hs
    rw [X.toCombMap.alpha_involutive e]
    exact ((X.faceBoundary (cell X k).face).mem_iff e).mp (arc.mem_cycle_of_mem_darts he)

end CellPocketKeptCell

namespace GloballyDistinguishedSectionFamily

variable {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The kept cell of the pocket between two cells, from the values of the relator words.**  Let
`a ≠ b` be selected regions joining the distinct cells `i` and `j`, and `K` a cell pocket walk whose
first side is the side of `b` leaving `Π_j`, whose second side is the side of `a` leaving `Π_i`,
and whose arc of `Π_i` spans the arc of `a`, a gap and the arc of `b`.  Let `P` be a pocket region
whose cycle is the walk.  If no relator word has value one, a relator cell lies in `P`. -/
theorem exists_kept_of_cellPocketRegion_of_value
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {i j : Fin S.diagram.rCellCount} {a b : RegionCandidate D eps S.diagram}
    (ha : a ∈ S.family) (hb : b ∈ S.family) (hab : a ≠ b) (hij : i ≠ j)
    (hai : a.JoinsCells i j) (hbi : b.JoinsCells i j) (K : CellPocketWalk D eps S.diagram i j)
    (hfirst : K.firstSide = b.sideFrom j) (hsecond : K.secondSide = a.sideFrom i)
    (h₁ : ∃ G₁ : CyclicArc (cellDarts S.diagram i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    (P : PocketRegion S.diagram) (hinner : P.inner.cycle = K.walk) :
    ∃ kept : Fin S.diagram.rCellCount, (cell S.diagram kept).face ∈ P.faces := by
  classical
  by_contra hno
  have hcells : ∀ C ∈ S.diagram.relatorCells, C.face ∉ P.faces := by
    intro C hC hmem
    obtain ⟨n, rfl⟩ := List.mem_iff_get.mp hC
    exact hno ⟨n, hmem⟩
  obtain ⟨G₁, hG₁⟩ := h₁
  have hcontained : ∀ x ∈ S.family, ¬ Disjoint x.1 P.faces → x.1 ⊆ P.faces :=
    fun x hxS hxmeet => RealizedRegionFamily.subset_of_not_disjoint_cellPocketRegion
      S.toRealizedRegionFamily K ha hb hfirst hsecond hvalue P hinner hxS hxmeet
  -- A region whose arc on `Π_i` lies on `t_1` meets the pocket.
  have hmeet : ∀ x ∈ S.family, x.JoinsCells i j →
      (∀ e ∈ x.cellArcList i, e ∈ K.firstArc.darts) → ¬ Disjoint x.1 P.faces := by
    intro x hxS hxi hsub
    obtain ⟨e, r, her⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos
      (RegionCandidate.cellArcList_length_pos (S.nondegenerate x hxS) i))
    have he : e ∈ x.cellArcList i := by
      rw [her]
      simp
    have hew : S.diagram.toCombMap.alpha e ∈ P.inner.cycle := by
      rw [hinner]
      simp only [CellPocketWalk.walk, List.mem_append]
      exact Or.inl (Or.inl (Or.inr
        (List.mem_map.mpr ⟨e, List.mem_reverse.mpr (hsub e he), rfl⟩)))
    exact Finset.not_disjoint_iff.mpr
      ⟨_, RegionCandidate.faceOf_alpha_mem_of_mem_cellArcList hxi he,
        ((P.inner.cycle_mem_iff _).mp hew).1⟩
  obtain ⟨A, hA⟩ : ∃ A : Finset (RegionCandidate D eps S.diagram),
      ∀ x, x ∈ A ↔ x ∈ S.family ∧ ¬ Disjoint x.1 P.faces :=
    ⟨S.family.filter fun x => ¬ Disjoint x.1 P.faces, fun _ => Finset.mem_filter⟩
  have haA : a ∈ A := (hA a).mpr ⟨ha, hmeet a ha hai fun e he => by
    rw [hG₁]
    exact List.mem_append_left _ (List.mem_append_left _ he)⟩
  have hbA : b ∈ A := (hA b).mpr ⟨hb, hmeet b hb hbi fun e he => by
    rw [hG₁]
    exact List.mem_append_right _ he⟩
  have hcard : 2 ≤ A.card :=
    (Finset.card_pair_eq_two_iff.mpr hab).ge.trans (Finset.card_le_card
      (Finset.insert_subset_iff.mpr ⟨haA, Finset.singleton_subset_iff.mpr hbA⟩))
  have hmemcyc : ∀ x : RegionCandidate D eps S.diagram, ∀ d ∈ x.2.sourceArc.reverseDarts ++
      targetBoundaryDarts S.diagram x.2.target x.2.targetArc, d ∈ x.2.boundary.cycle := by
    intro x d hd
    rw [x.2.boundary_decomposition]
    rcases List.mem_append.mp hd with h | h
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))
    · exact List.mem_append_left _ (List.mem_append_right _ h)
  have hbdcard : ∀ x : RegionCandidate D eps S.diagram,
      (x.2.sourceArc.reverseDarts ++
        targetBoundaryDarts S.diagram x.2.target x.2.targetArc).toFinset.card = x.weight := by
    intro x
    have hnd := x.2.boundary.cycle_nodup
    rw [x.2.boundary_decomposition] at hnd
    rw [List.toFinset_card_of_nodup (CellPocketKeptCell.nodup_four hnd).1, List.length_append,
      ContiguityGeometry.targetBoundaryDarts_length x.2]
    simp only [CyclicArc.reverseDarts, List.length_map, List.length_reverse,
      CyclicArc.darts_length, RegionCandidate.weight]
  have hdisj : (A : Set (RegionCandidate D eps S.diagram)).PairwiseDisjoint fun x =>
      (x.2.sourceArc.reverseDarts ++
        targetBoundaryDarts S.diagram x.2.target x.2.targetArc).toFinset := by
    intro x hx y hy hxy
    refine Finset.disjoint_left.mpr ?_
    intro d hdx hdy
    exact Finset.disjoint_left.mp
      (S.pairwise x ((hA x).mp (Finset.mem_coe.mp hx)).1 y ((hA y).mp (Finset.mem_coe.mp hy)).1
        hxy)
      ((x.2.boundary.cycle_mem_iff d).mp (hmemcyc x d (List.mem_toFinset.mp hdx))).1
      ((y.2.boundary.cycle_mem_iff d).mp (hmemcyc y d (List.mem_toFinset.mp hdy))).1
  -- The arc darts of the absorbed regions lie on `t_1` and `t_2`.
  have hsubT : A.biUnion (fun x => (x.2.sourceArc.reverseDarts ++
        targetBoundaryDarts S.diagram x.2.target x.2.targetArc).toFinset) ⊆
      (invDarts S.diagram K.firstArc.darts ++ invDarts S.diagram K.secondArc.darts).toFinset := by
    intro d hd
    obtain ⟨x, hx, hdx⟩ := Finset.mem_biUnion.mp hd
    have hdx' := List.mem_toFinset.mp hdx
    obtain ⟨hxS, hxmeet⟩ := (hA x).mp hx
    have hbd := (x.2.boundary.cycle_mem_iff d).mp (hmemcyc x d hdx')
    have hdP : S.diagram.toCombMap.faceOf d ∈ P.faces := hcontained x hxS hxmeet hbd.1
    have haP : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∉ P.faces := by
      rcases List.mem_append.mp hdx' with hs | ht
      · simp only [CyclicArc.reverseDarts, List.mem_map, List.mem_reverse] at hs
        obtain ⟨e, he, rfl⟩ := hs
        rw [S.diagram.toCombMap.alpha_involutive e,
          ((S.diagram.faceBoundary (cell S.diagram x.2.source).face).mem_iff e).mp
            (x.2.sourceArc.mem_cycle_of_mem_darts he)]
        exact hcells _ (cell_mem S.diagram x.2.source)
      · rcases CellPocketKeptCell.faceOf_alpha_of_mem_targetBoundaryDarts x.2.targetArc ht with
          h | ⟨k, h⟩
        · rw [h]
          exact P.outerFace_not_mem
        · rw [h]
          exact hcells _ (cell_mem S.diagram k)
    have hdw : d ∈ K.walk := by
      rw [← hinner]
      exact (P.inner.cycle_mem_iff d).mpr ⟨hdP, haP⟩
    have hnd := x.2.boundary.cycle_nodup
    rw [x.2.boundary_decomposition] at hnd
    simp only [CellPocketWalk.walk, List.mem_append] at hdw
    rcases hdw with ((h1 | h2) | h3) | h4
    · rw [hfirst] at h1
      by_cases hxb : x = b
      · rw [← hxb] at h1
        by_cases hs : x.2.source = j
        · rw [RegionCandidate.sideFrom, if_pos hs] at h1
          exact ((CellPocketKeptCell.nodup_four hnd).2.1 d hdx' h1).elim
        · rw [RegionCandidate.sideFrom, if_neg hs] at h1
          exact ((CellPocketKeptCell.nodup_four hnd).2.2 d hdx' h1).elim
      · exact (Finset.disjoint_left.mp (S.pairwise x hxS b hb hxb) hbd.1
          ((b.2.boundary.cycle_mem_iff d).mp
            (CellPocketWalkColour.mem_boundary_of_mem_sideFrom b j h1)).1).elim
    · exact List.mem_toFinset.mpr (List.mem_append_left _ h2)
    · rw [hsecond] at h3
      by_cases hxa : x = a
      · rw [← hxa] at h3
        by_cases hs : x.2.source = i
        · rw [RegionCandidate.sideFrom, if_pos hs] at h3
          exact ((CellPocketKeptCell.nodup_four hnd).2.1 d hdx' h3).elim
        · rw [RegionCandidate.sideFrom, if_neg hs] at h3
          exact ((CellPocketKeptCell.nodup_four hnd).2.2 d hdx' h3).elim
      · exact (Finset.disjoint_left.mp (S.pairwise x hxS a ha hxa) hbd.1
          ((a.2.boundary.cycle_mem_iff d).mp
            (CellPocketWalkColour.mem_boundary_of_mem_sideFrom a i h3)).1).elim
    · exact List.mem_toFinset.mpr (List.mem_append_right _ h4)
  have hweight : EstimatingSelection.familyWeight RegionCandidate.weight A ≤
      K.firstArc.length + K.secondArc.length := by
    unfold EstimatingSelection.familyWeight
    calc ∑ x ∈ A, x.weight
        = ∑ x ∈ A, (x.2.sourceArc.reverseDarts ++
            targetBoundaryDarts S.diagram x.2.target x.2.targetArc).toFinset.card :=
          Finset.sum_congr rfl fun x _ => (hbdcard x).symm
      _ = (A.biUnion fun x => (x.2.sourceArc.reverseDarts ++
            targetBoundaryDarts S.diagram x.2.target x.2.targetArc).toFinset).card :=
          (Finset.card_biUnion hdisj).symm
      _ ≤ (invDarts S.diagram K.firstArc.darts ++
            invDarts S.diagram K.secondArc.darts).toFinset.card :=
          Finset.card_le_card hsubT
      _ ≤ (invDarts S.diagram K.firstArc.darts ++ invDarts S.diagram K.secondArc.darts).length :=
          List.toFinset_card_le _
      _ = K.firstArc.length + K.secondArc.length := by
          simp only [List.length_append, invDarts, List.length_map, List.length_reverse,
            CyclicArc.darts_length]
  -- The merged face reads `t_1`, `s_2`, `t_2`, `s_1`.
  have hrot : (Surgery.InnerDiscRegion.ofPocketRegion P hcells).region.cycle.rotate
      K.firstSide.length = K.firstArc.reverseDarts ++ K.secondSide ++
        targetBoundaryDarts S.diagram (some j) K.secondArc ++ K.firstSide := by
    rw [Surgery.InnerDiscRegion.ofPocketRegion_region_cycle, hinner]
    show (K.firstSide ++ invDarts S.diagram K.firstArc.darts ++ K.secondSide ++
        invDarts S.diagram K.secondArc.darts).rotate K.firstSide.length =
      invDarts S.diagram K.firstArc.darts ++ K.secondSide ++
        invDarts S.diagram K.secondArc.darts ++ K.firstSide
    simp only [List.append_assoc, List.rotate_append_length_eq]
  refine S.false_of_disc_absorbed_section (Surgery.InnerDiscRegion.ofPocketRegion P hcells) A
    (fun x hx => ((hA x).mp hx).1) hcard
    (fun x hxS hxA => by
      by_contra h
      exact hxA ((hA x).mpr ⟨hxS, h⟩))
    ((Surgery.InnerDiscRegion.ofPocketRegion P hcells).mergedGeometry (target := some j)
      K.firstArc K.secondArc hrot K.secondSide_length_le K.firstSide_length_le
      K.secondSide_norm_le K.firstSide_norm_le) ?_ ?_ ?_ ?_ ?_
  · change Option.map (Surgery.InnerDiscRegion.ofPocketRegion P hcells).cellMap.indexEquiv
        (some j) ≠ some ((Surgery.InnerDiscRegion.ofPocketRegion P hcells).cellMap.indexEquiv i)
    intro h
    exact hij (by simpa using h.symm)
  · intro h
    rw [Surgery.InnerDiscRegion.mergedGeometry_target] at h
    simp at h
  · rw [Surgery.InnerDiscRegion.mergedGeometry_sourceArc_length]
    exact K.firstArc_pos
  · rw [Surgery.InnerDiscRegion.mergedGeometry_targetArc_length]
    exact K.secondArc_pos
  · rw [Surgery.InnerDiscRegion.mergedGeometry_sourceArc_length,
      Surgery.InnerDiscRegion.mergedGeometry_targetArc_length]
    exact hweight

/-- **The kept cell of the pocket between two cells at least area.**  With `a`, `b`, `K` and `P`
as in `exists_kept_of_cellPocketRegion_of_value`, if the diagram has least area, a relator cell
lies in `P`.  At least area no relator word has value one. -/
theorem exists_kept_of_cellPocketRegion_of_leastArea
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {i j : Fin S.diagram.rCellCount} {a b : RegionCandidate D eps S.diagram}
    (ha : a ∈ S.family) (hb : b ∈ S.family) (hab : a ≠ b) (hij : i ≠ j)
    (hai : a.JoinsCells i j) (hbi : b.JoinsCells i j) (K : CellPocketWalk D eps S.diagram i j)
    (hfirst : K.firstSide = b.sideFrom j) (hsecond : K.secondSide = a.sideFrom i)
    (h₁ : ∃ G₁ : CyclicArc (cellDarts S.diagram i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    (hlea : S.diagram.LeastArea) (P : PocketRegion S.diagram) (hinner : P.inner.cycle = K.walk) :
    ∃ kept : Fin S.diagram.rCellCount, (cell S.diagram kept).face ∈ P.faces :=
  S.exists_kept_of_cellPocketRegion_of_value ha hb hab hij hai hbi K hfirst hsecond h₁
    (fun C hC => DiscDiagram.leastArea_listVal_word_ne_one hlea C hC) P hinner

end GloballyDistinguishedSectionFamily

/-- **The pocket between two cells keeps a relator cell** (step 5 of the binder-5 route).  Two
distinct selected regions of a globally distinguished family joining the distinct cells `i` and `j`
give the cell pocket walk of `CellPocketWalk.exists_of_joinsCells`.  If the diagram has least area,
every pocket region whose cycle is that walk holds a relator cell. -/
def CellPocketKeptCellStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {eps : ℕ} {lambda c : ℝ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {i j : Fin S.diagram.rCellCount} {a b : RegionCandidate D eps S.diagram},
    a ∈ S.family → b ∈ S.family → a ≠ b → i ≠ j → a.JoinsCells i j → b.JoinsCells i j →
      ∃ K : CellPocketWalk D eps S.diagram i j,
        K.firstSide = b.sideFrom j ∧ K.secondSide = a.sideFrom i ∧
          (∃ G₁ : CyclicArc (cellDarts S.diagram i),
            K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i) ∧
          (∃ G₂ : CyclicArc (cellDarts S.diagram j),
            K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) ∧
          (S.diagram.LeastArea → ∀ P : PocketRegion S.diagram, P.inner.cycle = K.walk →
            ∃ kept : Fin S.diagram.rCellCount, (cell S.diagram kept).face ∈ P.faces)

theorem cellPocketKeptCell : CellPocketKeptCellStatement.{u, w, v} := by
  intro G _ Lambda W D eps lambda c Delta cuts S i j a b ha hb hab hij hai hbi
  obtain ⟨K, hfirst, hsecond, h₁, h₂⟩ :=
    CellPocketWalk.exists_of_joinsCells S.toRealizedSectionFamily ha hb hab hai hbi
  exact ⟨K, hfirst, hsecond, h₁, h₂, fun hlea P hinner =>
    S.exists_kept_of_cellPocketRegion_of_leastArea ha hb hab hij hai hbi K hfirst hsecond h₁ hlea P
      hinner⟩

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketKeptCell.nodup_four
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketKeptCell.faceOf_alpha_of_mem_targetBoundaryDarts
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.exists_kept_of_cellPocketRegion_of_value
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.exists_kept_of_cellPocketRegion_of_leastArea
#audit_closed_axioms GroupApproximation.GGT.VanKampen.cellPocketKeptCell
