import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.Inside
import GroupApproximation.Meta.AxiomGuard

/-!
# The quadrant move for a lobe with the rest of the cycle off its side

Lane gl-p10-92.  Helper theorems for `P10FilterMoveExists.p10FM_QuadrantMoveStatement`: the full
conclusion of that statement, for a given cyclic block `B` of the boundary cycle `c` of `F`, under
explicit hypotheses on `B`.  They do not use the rose premises, nor planarity.

Here `B` is a closed walk, some dart of `c` is off `B`, every dart of `c` off `B` has its face off
the side `sideFaces M B`, and no dart of the two arcs is on `B`.  A dart `d ∈ B` has its face on
the side, by definition of `sideFaces`.

* `p10QM_move_TT` (quadrant `p = q = true`, when `k` is off the side): the move removes exactly
  `B`, keeps both arcs whole, and keeps the closed walk `c` minus `B`.
* `p10QM_move_FT` (quadrant `p = false, q = true`, when `k` is on the side): the move keeps
  exactly `B` and drops both arcs.

All PROVED.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10FilterMoveExists

/-- A dart of `B` has its face on the side of `B`. -/
theorem p10QM_faceOf_mem_sideFaces (M : CombMap.{v}) {B : List M.Dart} {d : M.Dart}
    (hd : d ∈ B) : M.faceOf d ∈ sideFaces M B :=
  (mem_sideFaces_iff M B d).mpr ⟨d, hd, Relation.EqvGen.refl _⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QM_faceOf_mem_sideFaces

/-- **Quadrant `p = q = true` for a lobe with the rest of `c` off its side and `k` off it.** -/
theorem p10QM_move_TT (M : CombMap.{v}) (F : Finset M.Face) (c : BoundaryCycle M F)
    (o s k : M.Face) (bs : FaceBoundary M s) (bo : FaceBoundary M o) (a : CyclicArc bs.darts)
    (b : CyclicArc (bo.darts.reverse.map M.alpha)) (s₁ s₂ B : List M.Dart)
    (hc : IsClosedDartWalk M c.cycle)
    (hsplit : c.cycle = s₁ ++ a.darts.reverse.map M.alpha ++ s₂ ++ b.darts)
    (hblk : p10QM_CyclicBlock c.cycle B) (hBw : IsClosedDartWalk M B)
    (hP : ∃ d ∈ c.cycle, d ∉ B) (hout : ∀ d ∈ c.cycle, d ∉ B → M.faceOf d ∉ sideFaces M B)
    (ho : o ∉ F) (hs : s ∉ F) (hk : k ∉ sideFaces M B)
    (hla' : ∀ d ∈ a.darts.reverse.map M.alpha, d ∉ B) (hlb' : ∀ d ∈ b.darts, d ∉ B) :
    ∃ (B : List M.Dart) (p q : Bool), (∀ d ∈ B, d ∈ c.cycle) ∧
      ¬p10FM_InZ M F B p q o ∧ ¬p10FM_InZ M F B p q s ∧ ¬p10FM_InZ M F B p q k ∧
      (∃ y ∈ c.cycle, movePred M (p10FM_z M F B p q) y = false) ∧
      (a.darts.reverse.map M.alpha).filter (movePred M (p10FM_z M F B p q)) <:+:
        a.darts.reverse.map M.alpha ∧
      b.darts.filter (movePred M (p10FM_z M F B p q)) <+: b.darts ∧
      IsClosedDartWalk M (c.cycle.filter (movePred M (p10FM_z M F B p q))) := by
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
  have hfa : (a.darts.reverse.map M.alpha).filter (movePred M (p10FM_z M F B true true)) =
      a.darts.reverse.map M.alpha := List.filter_eq_self.mpr fun d hd =>
    (hkeep d (hla d hd).1).mpr (hla' d hd)
  have hfb : b.darts.filter (movePred M (p10FM_z M F B true true)) = b.darts :=
    List.filter_eq_self.mpr fun d hd => (hkeep d (hlb d hd).1).mpr (hlb' d hd)
  have hne : B ≠ [] := by
    obtain ⟨hne, -, -⟩ := hBw
    exact hne
  refine ⟨B, true, true, hBc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨-, h⟩
    exact ho (h.mpr rfl)
  · rintro ⟨-, h⟩
    exact hs (h.mpr rfl)
  · rintro ⟨h, -⟩
    exact hk (h.mpr rfl)
  · obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil B hne
    exact ⟨y, hBc y hy, Bool.eq_false_iff.mpr fun h => (hkeep y (hBc y hy)).mp h hy⟩
  · rw [hfa]
    exact List.infix_refl _
  · rw [hfb]
    exact List.prefix_refl _
  · exact p10QM_closed_filter_remove hc c.cycle_nodup hblk hBw hP hkeep

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QM_move_TT

/-- **Quadrant `p = false, q = true` for a lobe with the rest of `c` off its side and `k` on
it.** -/
theorem p10QM_move_FT (M : CombMap.{v}) (F : Finset M.Face) (c : BoundaryCycle M F)
    (o s k : M.Face) (bs : FaceBoundary M s) (bo : FaceBoundary M o) (a : CyclicArc bs.darts)
    (b : CyclicArc (bo.darts.reverse.map M.alpha)) (s₁ s₂ B : List M.Dart)
    (hsplit : c.cycle = s₁ ++ a.darts.reverse.map M.alpha ++ s₂ ++ b.darts)
    (hblk : p10QM_CyclicBlock c.cycle B) (hBw : IsClosedDartWalk M B)
    (hP : ∃ d ∈ c.cycle, d ∉ B) (hout : ∀ d ∈ c.cycle, d ∉ B → M.faceOf d ∉ sideFaces M B)
    (ho : o ∉ F) (hs : s ∉ F) (hk : k ∈ sideFaces M B)
    (hla' : ∀ d ∈ a.darts.reverse.map M.alpha, d ∉ B) (hlb' : ∀ d ∈ b.darts, d ∉ B) :
    ∃ (B : List M.Dart) (p q : Bool), (∀ d ∈ B, d ∈ c.cycle) ∧
      ¬p10FM_InZ M F B p q o ∧ ¬p10FM_InZ M F B p q s ∧ ¬p10FM_InZ M F B p q k ∧
      (∃ y ∈ c.cycle, movePred M (p10FM_z M F B p q) y = false) ∧
      (a.darts.reverse.map M.alpha).filter (movePred M (p10FM_z M F B p q)) <:+:
        a.darts.reverse.map M.alpha ∧
      b.darts.filter (movePred M (p10FM_z M F B p q)) <+: b.darts ∧
      IsClosedDartWalk M (c.cycle.filter (movePred M (p10FM_z M F B p q))) := by
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
  have hfa : (a.darts.reverse.map M.alpha).filter (movePred M (p10FM_z M F B false true)) =
      [] := List.filter_eq_nil_iff.mpr fun d hd h =>
    hla' d hd ((hkeep d (hla d hd).1).mp h)
  have hfb : b.darts.filter (movePred M (p10FM_z M F B false true)) = [] :=
    List.filter_eq_nil_iff.mpr fun d hd h => hlb' d hd ((hkeep d (hlb d hd).1).mp h)
  refine ⟨B, false, true, hBc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨-, h⟩
    exact ho (h.mpr rfl)
  · rintro ⟨-, h⟩
    exact hs (h.mpr rfl)
  · rintro ⟨h, -⟩
    exact Bool.false_ne_true (h.mp hk)
  · obtain ⟨y, hy, hyB⟩ := hP
    exact ⟨y, hy, Bool.eq_false_iff.mpr fun h => hyB ((hkeep y hy).mp h)⟩
  · rw [hfa]
    exact List.nil_infix
  · rw [hfb]
    exact List.nil_prefix
  · exact p10QM_closed_filter_keep c.cycle_nodup hblk hBw hkeep

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QM_move_FT

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove
