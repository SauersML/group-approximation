import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.ArcStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.Assembly
import GroupApproximation.Meta.AxiomGuard

/-!
# The witness lemma for good lobes that meet the arcs

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane nm-osin94, a sub-step of lane
nm-gl03d's step 2 (interface `P10LocalSelect/ArcStatement`).

* `p10LS_move_of_goodArc`: the conclusion of `P10FilterMoveExists.p10FM_QuadrantMoveStatement` for
  a lobe `B` with `p10LS_GoodArc`.  This is `P10QuadrantMove.p10QM_move_TT` (quadrant
  `p = q = true`, when `k` is off the side) and `p10QM_move_FT` (`p = false, q = true`, when `k` is
  on it), with the arcs allowed to meet `B`.  On darts of `c` the keep predicate of the move is
  `d ∉ B`, respectively `d ∈ B` (`p10QM_movePred_TT` / `_FT`), and the arcs lie in `c`
  (`p10QM_arc_facts`), so `List.filter_congr` turns the two arc clauses into those of
  `p10LS_GoodArc`.
* `p10LS_quadrantMove_of_selectionArc`: `p10FM_QuadrantMoveStatement` from
  `p10LS_SelectionArcStatement`.  A good lobe is dispatched as in
  `p10LS_quadrantMove_of_selection` (`P10LocalSelect/Assembly`, lane ms-nm-uncond-b); a good lobe
  meeting the arcs goes through `p10LS_move_of_goodArc`.

Both are proved.  The selection statement itself is **OPEN** (nm-gl03d, step 2).

## Manuscript status

Infrastructure for `thm:hull` (Osin's Lemma 4.4 at least-area diagrams, residual 10).  It certifies
no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10FilterMoveExists
  P10QuadrantMove

open scoped Classical

/-- **The quadrant move for a good lobe meeting the arcs.** -/
theorem p10LS_move_of_goodArc (M : CombMap.{v}) (F : Finset M.Face) (c : BoundaryCycle M F)
    (o s k : M.Face) (bs : FaceBoundary M s) (bo : FaceBoundary M o) (a : CyclicArc bs.darts)
    (b : CyclicArc (bo.darts.reverse.map M.alpha)) (s₁ s₂ B : List M.Dart)
    (hc : IsClosedDartWalk M c.cycle)
    (hsplit : c.cycle = s₁ ++ a.darts.reverse.map M.alpha ++ s₂ ++ b.darts)
    (ho : o ∉ F) (hs : s ∉ F)
    (hG : p10LS_GoodArc M F c k (a.darts.reverse.map M.alpha) b.darts B) :
    ∃ (B : List M.Dart) (p q : Bool), (∀ d ∈ B, d ∈ c.cycle) ∧
      ¬p10FM_InZ M F B p q o ∧ ¬p10FM_InZ M F B p q s ∧ ¬p10FM_InZ M F B p q k ∧
      (∃ y ∈ c.cycle, movePred M (p10FM_z M F B p q) y = false) ∧
      (a.darts.reverse.map M.alpha).filter (movePred M (p10FM_z M F B p q)) <:+:
        a.darts.reverse.map M.alpha ∧
      b.darts.filter (movePred M (p10FM_z M F B p q)) <+: b.darts ∧
      IsClosedDartWalk M (c.cycle.filter (movePred M (p10FM_z M F B p q))) := by
  obtain ⟨hblk, hBw, hP, hout, ⟨hkB, hfa, hfb⟩ | ⟨hkB, hfa, hfb⟩⟩ := hG
  · -- `k` off the side: quadrant `p = q = true`, the move removes exactly `B`.
    have hBc := p10QM_cyclicBlock_subset hblk
    obtain ⟨hla, hlb⟩ := p10QM_arc_facts M c a b hsplit
    have hkeep : ∀ d ∈ c.cycle, movePred M (p10FM_z M F B true true) d = true ↔ d ∉ B := by
      intro d hd
      rw [p10QM_movePred_TT M c B hd]
      constructor
      · intro h hdB
        exact h (p10QM_faceOf_mem_sideFaces M hdB)
      · intro hdB
        exact hout d hd hdB
    have hA : (a.darts.reverse.map M.alpha).filter (movePred M (p10FM_z M F B true true)) =
        (a.darts.reverse.map M.alpha).filter (fun d => decide (d ∉ B)) :=
      List.filter_congr fun d hd =>
        Bool.eq_iff_iff.mpr ((hkeep d (hla d hd).1).trans decide_eq_true_iff.symm)
    have hT : b.darts.filter (movePred M (p10FM_z M F B true true)) =
        b.darts.filter (fun d => decide (d ∉ B)) :=
      List.filter_congr fun d hd =>
        Bool.eq_iff_iff.mpr ((hkeep d (hlb d hd).1).trans decide_eq_true_iff.symm)
    have hne : B ≠ [] := by
      obtain ⟨hne, -, -⟩ := hBw
      exact hne
    refine ⟨B, true, true, hBc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro ⟨-, h⟩
      exact ho (h.mpr rfl)
    · rintro ⟨-, h⟩
      exact hs (h.mpr rfl)
    · rintro ⟨h, -⟩
      exact hkB (h.mpr rfl)
    · obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil B hne
      exact ⟨y, hBc y hy, Bool.eq_false_iff.mpr fun h => (hkeep y (hBc y hy)).mp h hy⟩
    · rw [hA]
      exact hfa
    · rw [hT]
      exact hfb
    · exact p10QM_closed_filter_remove hc c.cycle_nodup hblk hBw hP hkeep
  · -- `k` on the side: quadrant `p = false, q = true`, the move keeps exactly `B`.
    have hBc := p10QM_cyclicBlock_subset hblk
    obtain ⟨hla, hlb⟩ := p10QM_arc_facts M c a b hsplit
    have hkeep : ∀ d ∈ c.cycle, movePred M (p10FM_z M F B false true) d = true ↔ d ∈ B := by
      intro d hd
      rw [p10QM_movePred_FT M c B hd]
      constructor
      · intro h
        by_contra hdB
        exact hout d hd hdB h
      · intro hdB
        exact p10QM_faceOf_mem_sideFaces M hdB
    have hA : (a.darts.reverse.map M.alpha).filter (movePred M (p10FM_z M F B false true)) =
        (a.darts.reverse.map M.alpha).filter (fun d => decide (d ∈ B)) :=
      List.filter_congr fun d hd =>
        Bool.eq_iff_iff.mpr ((hkeep d (hla d hd).1).trans decide_eq_true_iff.symm)
    have hT : b.darts.filter (movePred M (p10FM_z M F B false true)) =
        b.darts.filter (fun d => decide (d ∈ B)) :=
      List.filter_congr fun d hd =>
        Bool.eq_iff_iff.mpr ((hkeep d (hlb d hd).1).trans decide_eq_true_iff.symm)
    refine ⟨B, false, true, hBc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro ⟨-, h⟩
      exact ho (h.mpr rfl)
    · rintro ⟨-, h⟩
      exact hs (h.mpr rfl)
    · rintro ⟨h, -⟩
      exact Bool.false_ne_true (h.mp hkB)
    · obtain ⟨y, hy, hyB⟩ := hP
      exact ⟨y, hy, Bool.eq_false_iff.mpr fun h => hyB ((hkeep y hy).mp h)⟩
    · rw [hA]
      exact hfa
    · rw [hT]
      exact hfb
    · exact p10QM_closed_filter_keep c.cycle_nodup hblk hBw hkeep

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.p10LS_move_of_goodArc

/-- **The quadrant move from the local selection with arc-meeting lobes.**
`p10FM_QuadrantMoveStatement` from `p10LS_SelectionArcStatement`, which is OPEN. -/
theorem p10LS_quadrantMove_of_selectionArc (h : p10LS_SelectionArcStatement.{v}) :
    p10FM_QuadrantMoveStatement.{v} := by
  intro M F c o s k bs bo a b s₁ s₂ hM hc hpin hnf hcross ho hs hso hk ha hb hsplit
  obtain ⟨B, hB | hB⟩ :=
    h M F c o s k bs bo a b s₁ s₂ hM hc hpin hnf hcross ho hs hso hk ha hb hsplit
  · rcases hB with ⟨hblk, hBs, hP, hin, ⟨hoB, hsB⟩ | ⟨hoB, hsB⟩⟩ |
        ⟨hblk, hBw, hP, hout, hla, hlb⟩ |
        ⟨hBs, hBc, ⟨v0, hU⟩, hPin, ⟨hoB, hsB⟩ | ⟨hoB, hsB⟩⟩ |
        ⟨hBs, hBc, ⟨v0, hU⟩, hPout, ⟨hkB, hfa, hfb⟩ | ⟨hkB, hfa, hfb⟩⟩
    · exact p10QM_move_FF M F c o s k bs bo a b s₁ s₂ B hM hc hk hsplit hblk hBs hP hin hoB hsB
    · exact p10QM_move_TF M F c o s k bs bo a b s₁ s₂ B hM hk hsplit hblk hBs hP hin hoB hsB
    · by_cases hkB : k ∈ sideFaces M B
      · exact p10QM_move_FT M F c o s k bs bo a b s₁ s₂ B hsplit hblk hBw hP hout ho hs hkB
          hla hlb
      · exact p10QM_move_TT M F c o s k bs bo a b s₁ s₂ B hc hsplit hblk hBw hP hout ho hs hkB
          hla hlb
    · exact p10QS_move_untouched_FF M F c o s k bs bo a b s₁ s₂ B hM hc hk hsplit hBs hBc hU
        hPin hoB hsB
    · exact p10QS_move_untouched_TF M F c o s k bs bo a b s₁ s₂ B hM hc hk hsplit hBs hBc hU
        hPin hoB hsB
    · exact p10QS_move_untouched_TT M F c o s k bs bo a b B hM hc hBs hBc hU hPout ho hs hkB hfa
        hfb
    · exact p10QS_move_untouched_FT M F c o s k bs bo a b B hM hc hBs hBc hU hPout ho hs hkB hfa
        hfb
  · exact p10LS_move_of_goodArc M F c o s k bs bo a b s₁ s₂ B hc hsplit ho hs hB

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.p10LS_quadrantMove_of_selectionArc
