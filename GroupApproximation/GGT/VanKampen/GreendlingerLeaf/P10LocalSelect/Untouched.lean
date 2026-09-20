import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.Statement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantClose.ArcUniform
import GroupApproximation.Meta.AxiomGuard

/-!
# An untouched simple lobe off both arcs is a good lobe (step 2, second case)

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull` in
`non_mf_groups_exist.tex` (around line 2121); certifies no printed sentence on its own.

Step 2 of the local selection (`P10LocalSelect.p10LS_SelectionStatement`) chooses a lobe `B` of
the boundary cycle `c`.  This module handles a simple closed walk `B ⊆ c` that the rest of `c`
meets only at one vertex `v0` (`P10QuadrantMove.p10QS_Untouched`), that misses both arcs, and
that misses some dart of `c`.  Unlike `P10LocalSelect.OneSided`, `B` need not be a block of `c`,
and the rest of `c` may lie on both sides of `B`.

* If some dart of `c` off `B` has its face off the side of `B`, then `B` is case 4 of
  `p10LS_Good`.  The arc clauses hold for every quadrant, because the arcs miss `B`
  (`P10QuadrantMove.p10QC_arc_filters`).
* Otherwise every dart of `c` off `B` has its face on the side.  A dart of each arc is then on
  the side, and so is its reverse face (`s` for `a⁻¹`, `o` for `b`; `p10QM_side_alpha_iff`).
  That is case 3.

`p10LS_good_of_untouchedArcsOff` is PROVED.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10FilterMoveExists
  P10QuadrantMove

/-- **An untouched simple lobe off both arcs is a good lobe** (Osin 9.7(b), `thm:hull`
infrastructure).  The arcs are `A = a⁻¹` and `T = b` of a split `c = s₁ ++ A ++ s₂ ++ T`. -/
theorem p10LS_good_of_untouchedArcsOff {M : CombMap.{v}} {F : Finset M.Face}
    (c : BoundaryCycle M F) {o s k : M.Face} {bs : FaceBoundary M s} {bo : FaceBoundary M o}
    (a : CyclicArc bs.darts) (b : CyclicArc (bo.darts.reverse.map M.alpha))
    {s₁ s₂ B : List M.Dart}
    (hsplit : c.cycle = s₁ ++ a.darts.reverse.map M.alpha ++ s₂ ++ b.darts)
    (hB : IsSimpleClosedWalk M B) (hBc : ∀ e ∈ B, e ∈ c.cycle) {v0 : M.Vertex}
    (hU : p10QS_Untouched M c.cycle B v0) (hP : ∃ d ∈ c.cycle, d ∉ B)
    (hA : ∀ d ∈ a.darts.reverse.map M.alpha, d ∉ B) (hT : ∀ d ∈ b.darts, d ∉ B)
    (hAne : a.darts.reverse.map M.alpha ≠ []) (hTne : b.darts ≠ []) :
    p10LS_Good M F c o s k (a.darts.reverse.map M.alpha) b.darts B := by
  by_cases hex : ∃ d ∈ c.cycle, d ∉ B ∧ M.faceOf d ∉ sideFaces M B
  · -- A dart of the rest is off the side: case 4, with the arc clauses of every quadrant.
    refine Or.inr (Or.inr (Or.inr ⟨hB, hBc, ⟨v0, hU⟩, hex, ?_⟩))
    by_cases hk : k ∈ sideFaces M B
    · exact Or.inr ⟨hk, p10QC_arc_filters M c a b hsplit hBc false true hA hT⟩
    · exact Or.inl ⟨hk, p10QC_arc_filters M c a b hsplit hBc true true hA hT⟩
  · -- The whole rest is on the side: case 3, with `o` and `s` on the side.
    have hin : ∀ d ∈ c.cycle, d ∉ B → M.faceOf d ∈ sideFaces M B := by
      intro d hd hdB
      by_contra h
      exact hex ⟨d, hd, hdB, h⟩
    obtain ⟨harc, hbrc⟩ := p10QM_arc_facts M c a b hsplit
    have hrev : ∀ d ∈ c.cycle, d ∉ B →
        (M.faceOf d ∈ sideFaces M B ↔ M.faceOf (M.alpha d) ∈ sideFaces M B) := by
      intro d hd hdB
      exact p10QM_side_alpha_iff M B hdB fun h => p10QM_alpha_not_mem M c hd (hBc _ h)
    obtain ⟨da, hda⟩ := List.exists_mem_of_ne_nil _ hAne
    obtain ⟨dt, hdt⟩ := List.exists_mem_of_ne_nil _ hTne
    obtain ⟨hdac, hdas⟩ := harc da hda
    obtain ⟨hdtc, hdto⟩ := hbrc dt hdt
    have hs : s ∈ sideFaces M B := by
      rw [← hdas]
      exact (hrev da hdac (hA da hda)).mp (hin da hdac (hA da hda))
    have ho : o ∈ sideFaces M B := by
      rw [← hdto]
      exact (hrev dt hdtc (hT dt hdt)).mp (hin dt hdtc (hT dt hdt))
    obtain ⟨d, hd, hdB⟩ := hP
    exact Or.inr (Or.inr (Or.inl
      ⟨hB, hBc, ⟨v0, hU⟩, ⟨d, hd, hdB, hin d hd hdB⟩, Or.inl ⟨ho, hs⟩⟩))

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.p10LS_good_of_untouchedArcsOff
