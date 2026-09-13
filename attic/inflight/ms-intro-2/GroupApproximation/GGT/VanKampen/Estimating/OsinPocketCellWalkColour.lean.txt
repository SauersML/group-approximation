import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkColour
import GroupApproximation.Meta.AxiomGuard

/-!
# The pocket walk between two cells carries one colour

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): two distinct selected regions joining the
same two distinct cells `Π_i` and `Π_j` bound a subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`, where `s_1`, `s_2` are sides of the two regions and `t_1`, `t_2` are
arcs of `Π_i` and `Π_j`.

`ClosedWalkFaceColouring.exists_boundaryCycle_of_orient` makes a closed walk the boundary cycle of
a colour class, provided that every two-colouring changing colour exactly across the walk gives the
faces of all walk darts one colour.  This module proves that hypothesis for the pocket walk
`CellPocketWalk.walk` of two regions `a`, `b` joining `Π_i` and `Π_j`.  It is the cell-to-cell
analogue of `PocketWalkColour.walk_orient`, and step 4 of the producer route to
`MultipleEdgePocketRegionInput`.

* The faces of `a` are joined by edges inside `a`, and no walk dart has both of its faces in `a`,
  so `a` has one colour.  Likewise `b`.
* The arc of `Π_i` in the walk spans the arcs of `a` and of `b` on `Π_i`, and the arc of `Π_j`
  spans their arcs on `Π_j`.  So the walk crosses from each cell into each region, and both regions
  get the colour opposite to both cells.
* Every walk dart has its face in `a` or `b`, or crosses into `Π_i` or `Π_j`, so its face has the
  colour of `a` (`PocketWalkColour.orient_of_sides`).

Unlike the section-pocket case, all four crossings are arc darts of the walk, so no crossing into
the outer face is needed.

* `CellPocketWalkColour.walk_orient`: the pocket walk of two regions joining two cells carries one
  colour.
* `CellPocketWalkColourStatement` / `cellPocketWalkColour`: the same for the pocket walk given by
  `CellPocketWalk.exists_of_joinsCells`.

## Manuscript status

Infrastructure for `thm:hull` ("Hull's small cancellation theorem", through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Embedded HullSC WordMetric SimpleClosedWalkSides

universe u w v

namespace CellPocketWalkColour

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {lambda c : ℝ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- The side of a region leaving a cell lies on the boundary cycle of the region. -/
theorem mem_boundary_of_mem_sideFrom {X : DiscDiagram.{u, w, v} W}
    (a : RegionCandidate D eps X) (k : Fin X.rCellCount) {d : X.toCombMap.Dart}
    (hd : d ∈ a.sideFrom k) : d ∈ a.2.boundary.cycle := by
  rw [a.2.boundary_decomposition]
  simp only [List.mem_append]
  by_cases hs : a.2.source = k
  · rw [RegionCandidate.sideFrom, if_pos hs] at hd
    exact Or.inl (Or.inl (Or.inr hd))
  · rw [RegionCandidate.sideFrom, if_neg hs] at hd
    exact Or.inr hd

/-- A cell at one end of a selected region is not a face of the region. -/
theorem cell_face_not_mem (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {a : RegionCandidate D eps S.diagram} (ha : a ∈ S.family) {k : Fin S.diagram.rCellCount}
    (hk : a.2.source = k ∨ a.2.target = some k) : (cell S.diagram k).face ∉ a.1 := by
  obtain ⟨A, hA⟩ := RegionCandidate.exists_cellArc a hk
  obtain ⟨d, r, hdr⟩ := List.exists_cons_of_ne_nil
    (List.ne_nil_of_length_pos (RegionCandidate.cellArcList_length_pos (S.nondegenerate a ha) k))
  have hd : d ∈ a.cellArcList k := by
    rw [hdr]
    simp
  have hdface : S.diagram.toCombMap.faceOf d = (cell S.diagram k).face :=
    faceOf_of_mem_cellDarts (A.mem_cycle_of_mem_darts (by rw [hA]; exact hd))
  have hcycle : S.diagram.toCombMap.alpha d ∈ a.2.boundary.cycle := by
    rw [a.2.boundary_decomposition]
    simp only [List.mem_append]
    by_cases hs : a.2.source = k
    · rw [RegionCandidate.cellArcList, if_pos hs] at hd
      exact Or.inl (Or.inl (Or.inl (List.mem_map.mpr ⟨d, List.mem_reverse.mpr hd, rfl⟩)))
    · rw [RegionCandidate.cellArcList, if_neg hs] at hd
      refine Or.inl (Or.inr ?_)
      rw [targetBoundaryDarts_eq_invDarts (hk.resolve_left hs)]
      exact List.mem_map.mpr ⟨d, List.mem_reverse.mpr hd, rfl⟩
  have h := ((a.2.boundary.cycle_mem_iff _).mp hcycle).2
  rw [S.diagram.toCombMap.alpha_involutive d, hdface] at h
  exact h

/-- A selected region joining two cells crosses into each of its cells: some dart of its arc on
the cell is based at the cell and is crossed by `alpha` into the region. -/
theorem exists_crossDart (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {i j k : Fin S.diagram.rCellCount} {x : RegionCandidate D eps S.diagram} (hx : x ∈ S.family)
    (hij : x.JoinsCells i j) (hk : x.2.source = k ∨ x.2.target = some k) :
    ∃ s ∈ x.cellArcList k, S.diagram.toCombMap.faceOf s = (cell S.diagram k).face ∧
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha s) ∈ x.1 := by
  obtain ⟨A, hA⟩ := RegionCandidate.exists_cellArc x hk
  obtain ⟨s, r, hsr⟩ := List.exists_cons_of_ne_nil
    (List.ne_nil_of_length_pos (RegionCandidate.cellArcList_length_pos (S.nondegenerate x hx) k))
  have hs : s ∈ x.cellArcList k := by
    rw [hsr]
    simp
  refine ⟨s, hs, ?_, RegionCandidate.faceOf_alpha_mem_of_mem_cellArcList hij hs⟩
  exact faceOf_of_mem_cellDarts (A.mem_cycle_of_mem_darts (by rw [hA]; exact hs))

/-- **The four kinds of cell pocket walk dart.**  A dart of the pocket walk is a boundary dart of
`a` (the side `s_2`), a boundary dart of `b` (the side `s_1`), a dart crossing into `Π_i` (the
arc `t_1`), or a dart crossing into `Π_j` (the arc `t_2`). -/
theorem walk_cases {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}
    {a b : RegionCandidate D eps X} (K : CellPocketWalk D eps X i j)
    (hfirst : K.firstSide = b.sideFrom j) (hsecond : K.secondSide = a.sideFrom i)
    {e : X.toCombMap.Dart} (he : e ∈ K.walk) :
    (X.toCombMap.faceOf e ∈ a.1 ∧ X.toCombMap.faceOf (X.toCombMap.alpha e) ∉ a.1) ∨
      (X.toCombMap.faceOf e ∈ b.1 ∧ X.toCombMap.faceOf (X.toCombMap.alpha e) ∉ b.1) ∨
      X.toCombMap.faceOf (X.toCombMap.alpha e) = (cell X i).face ∨
      X.toCombMap.faceOf (X.toCombMap.alpha e) = (cell X j).face := by
  simp only [CellPocketWalk.walk, List.mem_append] at he
  rcases he with ((he | he) | he) | he
  · rw [hfirst] at he
    exact Or.inr (Or.inl
      ((b.2.boundary.cycle_mem_iff e).mp (mem_boundary_of_mem_sideFrom b j he)))
  · simp only [invDarts, List.mem_map, List.mem_reverse] at he
    obtain ⟨g, hg, rfl⟩ := he
    refine Or.inr (Or.inr (Or.inl ?_))
    rw [X.toCombMap.alpha_involutive g]
    exact faceOf_of_mem_cellDarts (K.firstArc.mem_cycle_of_mem_darts hg)
  · rw [hsecond] at he
    exact Or.inl ((a.2.boundary.cycle_mem_iff e).mp (mem_boundary_of_mem_sideFrom a i he))
  · simp only [invDarts, List.mem_map, List.mem_reverse] at he
    obtain ⟨g, hg, rfl⟩ := he
    refine Or.inr (Or.inr (Or.inr ?_))
    rw [X.toCombMap.alpha_involutive g]
    exact faceOf_of_mem_cellDarts (K.secondArc.mem_cycle_of_mem_darts hg)

/-- **The pocket walk between two cells carries one colour** (step 4 of the binder-5 route).  Let
`a`, `b` be distinct selected regions joining the cells `i` and `j`, and let `K` be a cell pocket
walk whose first side is the side of `b` leaving `Π_j`, whose second side is the side of `a`
leaving `Π_i`, whose arc of `Π_i` spans the arc of `a`, a gap and the arc of `b`, and whose arc of
`Π_j` spans the arc of `b`, a gap and the arc of `a`.  Then every two-colouring of the faces
changing colour exactly across the walk gives the faces of all walk darts one colour. -/
theorem walk_orient (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {i j : Fin S.diagram.rCellCount} {a b : RegionCandidate D eps S.diagram}
    (ha : a ∈ S.family) (hb : b ∈ S.family) (hab : a ≠ b)
    (hai : a.JoinsCells i j) (hbi : b.JoinsCells i j) (K : CellPocketWalk D eps S.diagram i j)
    (hfirst : K.firstSide = b.sideFrom j) (hsecond : K.secondSide = a.sideFrom i)
    (h₁ : ∃ G₁ : CyclicArc (cellDarts S.diagram i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    (h₂ : ∃ G₂ : CyclicArc (cellDarts S.diagram j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j)
    {faces : Finset S.diagram.toCombMap.Face}
    (hcol : ∀ d, ¬ (S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ faces ↔
      S.diagram.toCombMap.faceOf d ∈ faces) ↔ walkKeep S.diagram.toCombMap K.walk d) :
    ∀ d ∈ K.walk, ∀ e ∈ K.walk,
      (S.diagram.toCombMap.faceOf d ∈ faces ↔ S.diagram.toCombMap.faceOf e ∈ faces) := by
  have hdisj : Disjoint a.1 b.1 := S.pairwise a ha b hb hab
  have hia := cell_face_not_mem S ha hai.source_or_target_left
  have hja := cell_face_not_mem S ha hai.source_or_target_right
  have hib := cell_face_not_mem S hb hbi.source_or_target_left
  have hjb := cell_face_not_mem S hb hbi.source_or_target_right
  -- No walk dart lies inside `a` or inside `b`.
  have hoffa : ∀ e ∈ K.walk, S.diagram.toCombMap.faceOf e ∈ a.1 →
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha e) ∉ a.1 := by
    intro e he hea
    rcases walk_cases K hfirst hsecond he with h | h | h | h
    · exact h.2
    · exact absurd h.1 (Finset.disjoint_left.mp hdisj hea)
    · rw [h]
      exact hia
    · rw [h]
      exact hja
  have hoffb : ∀ e ∈ K.walk, S.diagram.toCombMap.faceOf e ∈ b.1 →
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha e) ∉ b.1 := by
    intro e he heb
    rcases walk_cases K hfirst hsecond he with h | h | h | h
    · exact absurd heb (Finset.disjoint_left.mp hdisj h.1)
    · exact h.2
    · rw [h]
      exact hib
    · rw [h]
      exact hjb
  have hacol : ∀ f ∈ a.1, ∀ g ∈ a.1, (f ∈ faces ↔ g ∈ faces) := fun f hf g hg =>
    PocketWalkColour.mem_iff_of_faceSetBoundary hcol a.2.boundary hoffa hf hg
  have hbcol : ∀ f ∈ b.1, ∀ g ∈ b.1, (f ∈ faces ↔ g ∈ faces) := fun f hf g hg =>
    PocketWalkColour.mem_iff_of_faceSetBoundary hcol b.2.boundary hoffb hf hg
  -- The walk crosses from each cell into each region.
  obtain ⟨G₁, hT₁⟩ := h₁
  obtain ⟨G₂, hT₂⟩ := h₂
  have hkeep₁ : ∀ s ∈ K.firstArc.darts, walkKeep S.diagram.toCombMap K.walk s := by
    intro s hs
    refine Or.inr ?_
    simp only [CellPocketWalk.walk, List.mem_append]
    exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨s, List.mem_reverse.mpr hs, rfl⟩)))
  have hkeep₂ : ∀ s ∈ K.secondArc.darts, walkKeep S.diagram.toCombMap K.walk s := by
    intro s hs
    refine Or.inr ?_
    simp only [CellPocketWalk.walk, List.mem_append]
    exact Or.inr (List.mem_map.mpr ⟨s, List.mem_reverse.mpr hs, rfl⟩)
  obtain ⟨sai, hsai, hsaif, hsaia⟩ := exists_crossDart S ha hai hai.source_or_target_left
  obtain ⟨sbi, hsbi, hsbif, hsbib⟩ := exists_crossDart S hb hbi hbi.source_or_target_left
  obtain ⟨saj, hsaj, hsajf, hsaja⟩ := exists_crossDart S ha hai hai.source_or_target_right
  obtain ⟨sbj, hsbj, hsbjf, hsbjb⟩ := exists_crossDart S hb hbi hbi.source_or_target_right
  have hsaiK : sai ∈ K.firstArc.darts := by
    rw [hT₁]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hsai)))
  have hsbiK : sbi ∈ K.firstArc.darts := by
    rw [hT₁]
    exact List.mem_append.mpr (Or.inr hsbi)
  have hsbjK : sbj ∈ K.secondArc.darts := by
    rw [hT₂]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hsbj)))
  have hsajK : saj ∈ K.secondArc.darts := by
    rw [hT₂]
    exact List.mem_append.mpr (Or.inr hsaj)
  have hai' : ¬ (S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha sai) ∈ faces ↔
      (cell S.diagram i).face ∈ faces) := by
    rw [← hsaif]
    exact (hcol sai).mpr (hkeep₁ sai hsaiK)
  have hbi' : ¬ (S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha sbi) ∈ faces ↔
      (cell S.diagram i).face ∈ faces) := by
    rw [← hsbif]
    exact (hcol sbi).mpr (hkeep₁ sbi hsbiK)
  have haj' : ¬ (S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha saj) ∈ faces ↔
      (cell S.diagram j).face ∈ faces) := by
    rw [← hsajf]
    exact (hcol saj).mpr (hkeep₂ saj hsajK)
  have hbj' : ¬ (S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha sbj) ∈ faces ↔
      (cell S.diagram j).face ∈ faces) := by
    rw [← hsbjf]
    exact (hcol sbj).mpr (hkeep₂ sbj hsbjK)
  refine PocketWalkColour.orient_of_sides hcol (A := fun f => f ∈ a.1 ∨ f ∈ b.1)
    (B := fun g => g = (cell S.diagram i).face ∨ g = (cell S.diagram j).face) ?_ ?_
    (Or.inl hsaia) (Or.inl rfl)
  · intro e he
    rcases walk_cases K hfirst hsecond he with h | h | h | h
    · exact Or.inl (Or.inl h.1)
    · exact Or.inl (Or.inr h.1)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro f g hf (rfl | rfl)
    · rcases hf with hf | hf
      · exact fun h => hai' ((hacol f hf _ hsaia).symm.trans h)
      · exact fun h => hbi' ((hbcol f hf _ hsbib).symm.trans h)
    · rcases hf with hf | hf
      · exact fun h => haj' ((hacol f hf _ hsaja).symm.trans h)
      · exact fun h => hbj' ((hbcol f hf _ hsbjb).symm.trans h)

end CellPocketWalkColour

/-- **The pocket walk between two cells carries one colour** (step 4 of the binder-5 route).  Two
distinct selected regions joining the cells `i` and `j` give the cell pocket walk of
`CellPocketWalk.exists_of_joinsCells`, and every two-colouring of the faces changing colour exactly
across that walk gives the faces of all walk darts one colour. -/
def CellPocketWalkColourStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {eps : ℕ} {lambda c : ℝ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {i j : Fin S.diagram.rCellCount} {a b : RegionCandidate D eps S.diagram},
    a ∈ S.family → b ∈ S.family → a ≠ b → a.JoinsCells i j → b.JoinsCells i j →
      ∃ K : CellPocketWalk D eps S.diagram i j,
        K.firstSide = b.sideFrom j ∧ K.secondSide = a.sideFrom i ∧
          (∃ G₁ : CyclicArc (cellDarts S.diagram i),
            K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i) ∧
          (∃ G₂ : CyclicArc (cellDarts S.diagram j),
            K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) ∧
          ∀ faces : Finset S.diagram.toCombMap.Face,
            (∀ d, ¬ (S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ faces ↔
              S.diagram.toCombMap.faceOf d ∈ faces) ↔ walkKeep S.diagram.toCombMap K.walk d) →
            ∀ d ∈ K.walk, ∀ e ∈ K.walk,
              (S.diagram.toCombMap.faceOf d ∈ faces ↔ S.diagram.toCombMap.faceOf e ∈ faces)

theorem cellPocketWalkColour : CellPocketWalkColourStatement.{u, w, v} := by
  intro G _ Lambda W D eps lambda c Delta cuts S i j a b ha hb hab hai hbi
  obtain ⟨K, hfirst, hsecond, h₁, h₂⟩ :=
    CellPocketWalk.exists_of_joinsCells S ha hb hab hai hbi
  exact ⟨K, hfirst, hsecond, h₁, h₂, fun _ hcol =>
    CellPocketWalkColour.walk_orient S ha hb hab hai hbi K hfirst hsecond h₁ h₂ hcol⟩

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalkColour.mem_boundary_of_mem_sideFrom
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalkColour.cell_face_not_mem
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalkColour.exists_crossDart
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalkColour.walk_cases
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalkColour.walk_orient
#audit_closed_axioms GroupApproximation.GGT.VanKampen.cellPocketWalkColour
