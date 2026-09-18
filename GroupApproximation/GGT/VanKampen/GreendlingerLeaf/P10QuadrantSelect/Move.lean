import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantSelect.Untouched
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.Inside
import GroupApproximation.Meta.AxiomGuard

/-!
# The quadrant moves `q = false` for an untouched lobe

Lane gl-p10-93.  Helper theorems for `P10FilterMoveExists.p10FM_QuadrantMoveStatement`: the full
conclusion of that statement, for a simple closed walk `B ⊆ c` untouched in `c` away from a
vertex `v0` (`p10QS_Untouched`), under explicit side hypotheses.  Unlike `p10QM_move_FF`,
`p10QM_move_TF`, the darts of `c` off `B` may lie on both sides of `B`, and `B` need not be a
cyclic block of `c`.  They do not use the rose premises.

* `p10QS_move_untouched_FF`: if `o, s` are on the side of `B` and some dart of `c` off `B` has
  its face on the side, the quadrant `p = q = false` works (it removes `B`).
* `p10QS_move_untouched_TF`: if `o, s` are off the side and some dart of `c` off `B` has its face
  on the side, the quadrant `p = true, q = false` works (it removes that dart, keeps `B`).

In both, both arcs are kept whole (their outer faces are `s` and `o`), and closedness is
`p10QS_closed_untouched`.  All PROVED.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10FilterMoveExists

/-- **Quadrant `p = q = false` for an untouched lobe with `o, s` on its side.** -/
theorem p10QS_move_untouched_FF (M : CombMap.{v}) (F : Finset M.Face) (c : BoundaryCycle M F)
    (o s k : M.Face) (bs : FaceBoundary M s) (bo : FaceBoundary M o) (a : CyclicArc bs.darts)
    (b : CyclicArc (bo.darts.reverse.map M.alpha)) (s₁ s₂ B : List M.Dart)
    (hM : M.IsPlanar) (hc : IsClosedDartWalk M c.cycle) (hk : k ∈ F)
    (hsplit : c.cycle = s₁ ++ a.darts.reverse.map M.alpha ++ s₂ ++ b.darts)
    (hB : IsSimpleClosedWalk M B) (hBc : ∀ e ∈ B, e ∈ c.cycle) {v0 : M.Vertex}
    (hU : p10QS_Untouched M c.cycle B v0)
    (hPin : ∃ d ∈ c.cycle, d ∉ B ∧ M.faceOf d ∈ sideFaces M B)
    (ho : o ∈ sideFaces M B) (hs : s ∈ sideFaces M B) :
    ∃ (B : List M.Dart) (p q : Bool), (∀ d ∈ B, d ∈ c.cycle) ∧
      ¬p10FM_InZ M F B p q o ∧ ¬p10FM_InZ M F B p q s ∧ ¬p10FM_InZ M F B p q k ∧
      (∃ y ∈ c.cycle, movePred M (p10FM_z M F B p q) y = false) ∧
      (a.darts.reverse.map M.alpha).filter (movePred M (p10FM_z M F B p q)) <:+:
        a.darts.reverse.map M.alpha ∧
      b.darts.filter (movePred M (p10FM_z M F B p q)) <+: b.darts ∧
      IsClosedDartWalk M (c.cycle.filter (movePred M (p10FM_z M F B p q))) := by
  obtain ⟨hla, hlb⟩ := p10QM_arc_facts M c a b hsplit
  have hfa : (a.darts.reverse.map M.alpha).filter (movePred M (p10FM_z M F B false false)) =
      a.darts.reverse.map M.alpha := List.filter_eq_self.mpr fun d hd =>
    (p10QM_movePred_FF M c B (hla d hd).1).mpr (by rw [(hla d hd).2]; exact hs)
  have hfb : b.darts.filter (movePred M (p10FM_z M F B false false)) = b.darts :=
    List.filter_eq_self.mpr fun d hd =>
      (p10QM_movePred_FF M c B (hlb d hd).1).mpr (by rw [(hlb d hd).2]; exact ho)
  obtain ⟨d, hd, hdB, hds⟩ := hPin
  refine ⟨B, false, false, hBc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨h, -⟩
    exact Bool.false_ne_true (h.mp ho)
  · rintro ⟨h, -⟩
    exact Bool.false_ne_true (h.mp hs)
  · rintro ⟨-, h⟩
    exact Bool.false_ne_true (h.mp hk)
  · obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil B hB.ne_nil
    exact ⟨y, hBc y hy, Bool.eq_false_iff.mpr fun h =>
      Bool.false_ne_true (((p10QS_movePred_on M hM c hB hBc false false hy).mp h).mpr rfl)⟩
  · exact (congrArg (· <:+: a.darts.reverse.map M.alpha) hfa).mpr (List.infix_refl _)
  · exact (congrArg (· <+: b.darts) hfb).mpr (List.prefix_refl _)
  · exact p10QS_closed_untouched M hM c hc hB hBc hU false false
      ⟨d, hd, (p10QS_movePred_off M c hBc false false hd hdB).mpr (iff_of_true hds rfl)⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QS_move_untouched_FF

/-- **Quadrant `p = true, q = false` for an untouched lobe with `o, s` off its side.** -/
theorem p10QS_move_untouched_TF (M : CombMap.{v}) (F : Finset M.Face) (c : BoundaryCycle M F)
    (o s k : M.Face) (bs : FaceBoundary M s) (bo : FaceBoundary M o) (a : CyclicArc bs.darts)
    (b : CyclicArc (bo.darts.reverse.map M.alpha)) (s₁ s₂ B : List M.Dart)
    (hM : M.IsPlanar) (hc : IsClosedDartWalk M c.cycle) (hk : k ∈ F)
    (hsplit : c.cycle = s₁ ++ a.darts.reverse.map M.alpha ++ s₂ ++ b.darts)
    (hB : IsSimpleClosedWalk M B) (hBc : ∀ e ∈ B, e ∈ c.cycle) {v0 : M.Vertex}
    (hU : p10QS_Untouched M c.cycle B v0)
    (hPin : ∃ d ∈ c.cycle, d ∉ B ∧ M.faceOf d ∈ sideFaces M B)
    (ho : o ∉ sideFaces M B) (hs : s ∉ sideFaces M B) :
    ∃ (B : List M.Dart) (p q : Bool), (∀ d ∈ B, d ∈ c.cycle) ∧
      ¬p10FM_InZ M F B p q o ∧ ¬p10FM_InZ M F B p q s ∧ ¬p10FM_InZ M F B p q k ∧
      (∃ y ∈ c.cycle, movePred M (p10FM_z M F B p q) y = false) ∧
      (a.darts.reverse.map M.alpha).filter (movePred M (p10FM_z M F B p q)) <:+:
        a.darts.reverse.map M.alpha ∧
      b.darts.filter (movePred M (p10FM_z M F B p q)) <+: b.darts ∧
      IsClosedDartWalk M (c.cycle.filter (movePred M (p10FM_z M F B p q))) := by
  obtain ⟨hla, hlb⟩ := p10QM_arc_facts M c a b hsplit
  have hfa : (a.darts.reverse.map M.alpha).filter (movePred M (p10FM_z M F B true false)) =
      a.darts.reverse.map M.alpha := List.filter_eq_self.mpr fun d hd =>
    (p10QM_movePred_TF M c B (hla d hd).1).mpr (by rw [(hla d hd).2]; exact hs)
  have hfb : b.darts.filter (movePred M (p10FM_z M F B true false)) = b.darts :=
    List.filter_eq_self.mpr fun d hd =>
      (p10QM_movePred_TF M c B (hlb d hd).1).mpr (by rw [(hlb d hd).2]; exact ho)
  obtain ⟨d, hd, hdB, hds⟩ := hPin
  refine ⟨B, true, false, hBc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨h, -⟩
    exact ho (h.mpr rfl)
  · rintro ⟨h, -⟩
    exact hs (h.mpr rfl)
  · rintro ⟨-, h⟩
    exact Bool.false_ne_true (h.mp hk)
  · exact ⟨d, hd, Bool.eq_false_iff.mpr fun h =>
      Bool.false_ne_true (((p10QS_movePred_off M c hBc true false hd hdB).mp h).mp hds).symm⟩
  · exact (congrArg (· <:+: a.darts.reverse.map M.alpha) hfa).mpr (List.infix_refl _)
  · exact (congrArg (· <+: b.darts) hfb).mpr (List.prefix_refl _)
  · obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil B hB.ne_nil
    exact p10QS_closed_untouched M hM c hc hB hBc hU true false
      ⟨y, hBc y hy, (p10QS_movePred_on M hM c hB hBc true false hy).mpr (by decide)⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QS_move_untouched_TF

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove
