import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalkColour
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketKeptCellAbsorbed
import GroupApproximation.Meta.AxiomGuard

/-!
# The regions meeting a pocket between two cells lie inside it

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): two distinct selected regions joining the
same two distinct cells `Π_i` and `Π_j` bound a subdiagram `Γ_1` with `∂Γ_1 = s_1 t_1 s_2 t_2`,
and "`Γ_1` contains all `Γ_{i,1}`'s".

This is the cell-to-cell analogue of `RealizedRegionFamily.subset_of_not_disjoint_pocketRegion`, a
step of the kept cell in the binder-5 route to `MultipleEdgePocketRegionInput`.  Let `K` be a cell
pocket walk whose first side is the side of `b` leaving `Π_j` and whose second side is the side of
`a` leaving `Π_i`, and let `P` be a pocket region whose cycle is the walk.  If no relator word has
value one, every selected region meeting `P` lies in `P`.  A dart of the region leaving the pocket
lies on the walk.  On a side it lies on the boundary of `b` or `a`.  On `t_1` or `t_2` it crosses
into `Π_i` or `Π_j`, whose words do not have value one, so they are not faces of a region.

* `RealizedRegionFamily.subset_of_not_disjoint_cellPocketRegion`: the containment.
* `CellPocketMeetsContainedStatement` / `cellPocketMeetsContained`: the same as a named
  proposition, proved.

## Manuscript status

Infrastructure for `thm:hull` ("Hull's small cancellation theorem", through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

namespace RealizedRegionFamily

variable {D : RelGenSet G Lambda} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}

/-- **A selected region meeting the pocket between two cells lies inside it.**  Let `K` be a cell
pocket walk of the diagram of a family whose first side is the side of the selected region `b`
leaving `Π_j` and whose second side is the side of the selected region `a` leaving `Π_i`, and let
`P` be a pocket region whose cycle is the walk.  If no relator word has value one, every selected
region meeting `P` lies in `P`. -/
theorem subset_of_not_disjoint_cellPocketRegion (S : RealizedRegionFamily D eps Delta)
    {i j : Fin S.diagram.rCellCount} (K : CellPocketWalk D eps S.diagram i j)
    {a b : RegionCandidate D eps S.diagram} (ha : a ∈ S.family) (hb : b ∈ S.family)
    (hfirst : K.firstSide = b.sideFrom j) (hsecond : K.secondSide = a.sideFrom i)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    (P : PocketRegion S.diagram) (hinner : P.inner.cycle = K.walk)
    {z : RegionCandidate D eps S.diagram} (hzS : z ∈ S.family)
    (hmeet : ¬ Disjoint z.1 P.faces) : z.1 ⊆ P.faces := by
  have hside : ∀ x ∈ S.family, ∀ d, d ∈ x.2.boundary.cycle →
      S.diagram.toCombMap.faceOf d ∈ z.1 →
        S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ z.1 → False := by
    intro x hxS d hdx hdz haz
    have hbd := (x.2.boundary.cycle_mem_iff d).mp hdx
    by_cases hzx : z = x
    · subst hzx
      exact hbd.2 haz
    · exact Finset.disjoint_left.mp (S.pairwise z hzS x hxS hzx) hdz hbd.1
  have hcell : ∀ k : Fin S.diagram.rCellCount, (cell S.diagram k).face ∉ z.1 := by
    intro k hkz
    have h := (z.2.boundary.all_gCells _ hkz).2
    rw [DiscDiagram.faceWord, ← S.diagram.relatorCell_word _ (cell_mem S.diagram k)] at h
    exact hvalue _ (cell_mem S.diagram k) h
  have hcross : ∀ d, S.diagram.toCombMap.faceOf d ∈ z.1 →
      S.diagram.toCombMap.faceOf d ∈ P.faces →
        S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ z.1 →
          S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ P.faces := by
    intro d hdz hdP haz
    by_contra haP
    have hdw : d ∈ K.walk := by
      rw [← hinner]
      exact (P.inner.cycle_mem_iff d).mpr ⟨hdP, haP⟩
    simp only [CellPocketWalk.walk, List.mem_append] at hdw
    rcases hdw with ((h1 | h2) | h3) | h4
    · rw [hfirst] at h1
      exact hside b hb d (CellPocketWalkColour.mem_boundary_of_mem_sideFrom b j h1) hdz haz
    · simp only [invDarts, List.mem_map, List.mem_reverse] at h2
      obtain ⟨e, he, rfl⟩ := h2
      rw [S.diagram.toCombMap.alpha_involutive e,
        faceOf_of_mem_cellDarts (K.firstArc.mem_cycle_of_mem_darts he)] at haz
      exact hcell i haz
    · rw [hsecond] at h3
      exact hside a ha d (CellPocketWalkColour.mem_boundary_of_mem_sideFrom a i h3) hdz haz
    · simp only [invDarts, List.mem_map, List.mem_reverse] at h4
      obtain ⟨e, he, rfl⟩ := h4
      rw [S.diagram.toCombMap.alpha_involutive e,
        faceOf_of_mem_cellDarts (K.secondArc.mem_cycle_of_mem_darts he)] at haz
      exact hcell j haz
  rcases z.2.boundary.subset_or_disjoint P.faces hcross with h | h
  · exact h
  · exact (hmeet h).elim

end RealizedRegionFamily

/-- **Meets implies contained, between two cells.**  For a cell pocket walk `K` of the diagram of a
family, with first side the side of the selected region `b` leaving `Π_j` and second side the side
of the selected region `a` leaving `Π_i`, and a pocket region `P` whose cycle is the walk: if no
relator word has value one, every selected region meeting `P` lies in `P`. -/
def CellPocketMeetsContainedStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (Delta : DiscDiagram.{u, w, v} W)
    (S : RealizedRegionFamily D eps Delta) (i j : Fin S.diagram.rCellCount)
    (K : CellPocketWalk D eps S.diagram i j) (a b : RegionCandidate D eps S.diagram),
    a ∈ S.family → b ∈ S.family → K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
      (∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) →
        ∀ P : PocketRegion S.diagram, P.inner.cycle = K.walk →
          ∀ z ∈ S.family, ¬ Disjoint z.1 P.faces → z.1 ⊆ P.faces

theorem cellPocketMeetsContained : CellPocketMeetsContainedStatement.{u, w, v} := by
  intro _ _ _ _ _ _ _ S _ _ K _ _ ha hb hfirst hsecond hvalue P hinner _ hzS hmeet
  exact RealizedRegionFamily.subset_of_not_disjoint_cellPocketRegion S K ha hb hfirst hsecond
    hvalue P hinner hzS hmeet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.RealizedRegionFamily.subset_of_not_disjoint_cellPocketRegion
#audit_closed_axioms GroupApproximation.GGT.VanKampen.cellPocketMeetsContained
