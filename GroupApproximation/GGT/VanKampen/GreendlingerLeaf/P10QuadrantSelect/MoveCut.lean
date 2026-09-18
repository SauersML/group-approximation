import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantSelect.Untouched
import GroupApproximation.Meta.AxiomGuard

/-!
# The quadrant moves `q = true` for an untouched lobe

Lane gl-p10-93.  Helper theorems for `P10FilterMoveExists.p10FM_QuadrantMoveStatement`: the full
conclusion of that statement for a simple closed walk `B ⊆ c` untouched in `c` away from a vertex
`v0` (`p10QS_Untouched`), in the two quadrants `q = true`.  These quadrants remove every dart of
`B` and every dart of `c` whose face is on the wrong side, so the arcs need not be kept whole;
their two arc clauses are taken as hypotheses (on small models they hold exactly when the kept
part of `a⁻¹` is an infix and the kept part of `b` a prefix, which is what the selection has to
check).  They do not use the rose premises.

* `p10QS_move_untouched_TT`: `k` off the side of `B`, some dart of `c` off `B` with its face
  off the side; quadrant `p = q = true`.
* `p10QS_move_untouched_FT`: `k` on the side of `B`, some dart of `c` off `B` with its face off
  the side; quadrant `p = false, q = true`.

Closedness is `p10QS_closed_untouched`.  All PROVED.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10FilterMoveExists

/-- **Quadrant `p = q = true` for an untouched lobe with `k` off its side.** -/
theorem p10QS_move_untouched_TT (M : CombMap.{v}) (F : Finset M.Face) (c : BoundaryCycle M F)
    (o s k : M.Face) (bs : FaceBoundary M s) (bo : FaceBoundary M o) (a : CyclicArc bs.darts)
    (b : CyclicArc (bo.darts.reverse.map M.alpha)) (B : List M.Dart)
    (hM : M.IsPlanar) (hc : IsClosedDartWalk M c.cycle)
    (hB : IsSimpleClosedWalk M B) (hBc : ∀ e ∈ B, e ∈ c.cycle) {v0 : M.Vertex}
    (hU : p10QS_Untouched M c.cycle B v0)
    (hPout : ∃ d ∈ c.cycle, d ∉ B ∧ M.faceOf d ∉ sideFaces M B)
    (ho : o ∉ F) (hs : s ∉ F) (hk : k ∉ sideFaces M B)
    (hfa : (a.darts.reverse.map M.alpha).filter (movePred M (p10FM_z M F B true true)) <:+:
      a.darts.reverse.map M.alpha)
    (hfb : b.darts.filter (movePred M (p10FM_z M F B true true)) <+: b.darts) :
    ∃ (B : List M.Dart) (p q : Bool), (∀ d ∈ B, d ∈ c.cycle) ∧
      ¬p10FM_InZ M F B p q o ∧ ¬p10FM_InZ M F B p q s ∧ ¬p10FM_InZ M F B p q k ∧
      (∃ y ∈ c.cycle, movePred M (p10FM_z M F B p q) y = false) ∧
      (a.darts.reverse.map M.alpha).filter (movePred M (p10FM_z M F B p q)) <:+:
        a.darts.reverse.map M.alpha ∧
      b.darts.filter (movePred M (p10FM_z M F B p q)) <+: b.darts ∧
      IsClosedDartWalk M (c.cycle.filter (movePred M (p10FM_z M F B p q))) := by
  obtain ⟨d, hd, hdB, hds⟩ := hPout
  refine ⟨B, true, true, hBc, ?_, ?_, ?_, ?_, hfa, hfb, ?_⟩
  · rintro ⟨-, h⟩
    exact ho (h.mpr rfl)
  · rintro ⟨-, h⟩
    exact hs (h.mpr rfl)
  · rintro ⟨h, -⟩
    exact hk (h.mpr rfl)
  · obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil B hB.ne_nil
    exact ⟨y, hBc y hy, Bool.eq_false_iff.mpr fun h =>
      Bool.false_ne_true (((p10QS_movePred_on M hM c hB hBc true true hy).mp h).mp rfl).symm⟩
  · exact p10QS_closed_untouched M hM c hc hB hBc hU true true
      ⟨d, hd, (p10QS_movePred_off M c hBc true true hd hdB).mpr
        (iff_of_false hds fun h => Bool.false_ne_true h.symm)⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QS_move_untouched_TT

/-- **Quadrant `p = false, q = true` for an untouched lobe with `k` on its side.** -/
theorem p10QS_move_untouched_FT (M : CombMap.{v}) (F : Finset M.Face) (c : BoundaryCycle M F)
    (o s k : M.Face) (bs : FaceBoundary M s) (bo : FaceBoundary M o) (a : CyclicArc bs.darts)
    (b : CyclicArc (bo.darts.reverse.map M.alpha)) (B : List M.Dart)
    (hM : M.IsPlanar) (hc : IsClosedDartWalk M c.cycle)
    (hB : IsSimpleClosedWalk M B) (hBc : ∀ e ∈ B, e ∈ c.cycle) {v0 : M.Vertex}
    (hU : p10QS_Untouched M c.cycle B v0)
    (hPout : ∃ d ∈ c.cycle, d ∉ B ∧ M.faceOf d ∉ sideFaces M B)
    (ho : o ∉ F) (hs : s ∉ F) (hk : k ∈ sideFaces M B)
    (hfa : (a.darts.reverse.map M.alpha).filter (movePred M (p10FM_z M F B false true)) <:+:
      a.darts.reverse.map M.alpha)
    (hfb : b.darts.filter (movePred M (p10FM_z M F B false true)) <+: b.darts) :
    ∃ (B : List M.Dart) (p q : Bool), (∀ d ∈ B, d ∈ c.cycle) ∧
      ¬p10FM_InZ M F B p q o ∧ ¬p10FM_InZ M F B p q s ∧ ¬p10FM_InZ M F B p q k ∧
      (∃ y ∈ c.cycle, movePred M (p10FM_z M F B p q) y = false) ∧
      (a.darts.reverse.map M.alpha).filter (movePred M (p10FM_z M F B p q)) <:+:
        a.darts.reverse.map M.alpha ∧
      b.darts.filter (movePred M (p10FM_z M F B p q)) <+: b.darts ∧
      IsClosedDartWalk M (c.cycle.filter (movePred M (p10FM_z M F B p q))) := by
  obtain ⟨d, hd, hdB, hds⟩ := hPout
  refine ⟨B, false, true, hBc, ?_, ?_, ?_, ?_, hfa, hfb, ?_⟩
  · rintro ⟨-, h⟩
    exact ho (h.mpr rfl)
  · rintro ⟨-, h⟩
    exact hs (h.mpr rfl)
  · rintro ⟨h, -⟩
    exact Bool.false_ne_true (h.mp hk)
  · exact ⟨d, hd, Bool.eq_false_iff.mpr fun h =>
      hds (((p10QS_movePred_off M c hBc false true hd hdB).mp h).mpr rfl)⟩
  · obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil B hB.ne_nil
    exact p10QS_closed_untouched M hM c hc hB hBc hU false true
      ⟨y, hBc y hy, (p10QS_movePred_on M hM c hB hBc false true hy).mpr (by decide)⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QS_move_untouched_FT

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove
