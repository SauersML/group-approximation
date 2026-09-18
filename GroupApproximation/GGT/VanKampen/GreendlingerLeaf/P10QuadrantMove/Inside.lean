import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.Block
import GroupApproximation.Meta.AxiomGuard

/-!
# The quadrant move for a lobe with the rest of the cycle on its side

Lane gl-p10-92.  Helper theorems for `P10FilterMoveExists.p10FM_QuadrantMoveStatement`: the full
conclusion of that statement, for a given cyclic block `B` of the boundary cycle `c` of `F`, under
explicit hypotheses on `B`.  They do not use the rose premises (`¬Unpinched`, first turns,
crossings).

Here `B` is a simple closed walk in the planar map `M` (a lobe of `c`), some dart of `c` is off
`B`, and every dart of `c` off `B` has its face on the side `sideFaces M B`.  By the Jordan fact
`IsSimpleClosedWalk.isBoundaryDart_sideFaces_iff`, a dart `d ∈ B` has the face of `alpha d` off
the side; a dart `d ∈ c` off `B` has the face of `alpha d` on the side (`p10QM_side_alpha_iff`).

* `p10QM_move_FF` (quadrant `p = q = false`, when `o, s` are on the side): the move removes
  exactly `B`, keeps both arcs whole, and keeps the closed walk `c` minus `B`.
* `p10QM_move_TF` (quadrant `p = true, q = false`, when `o, s` are off the side): the move keeps
  exactly `B` and both arcs whole.

All PROVED.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10FilterMoveExists

section Arcs

variable (M : CombMap.{v})

/-- A dart of `l.reverse.map alpha`, for darts `l` on the boundary of `f`, has its reverse on
`f`. -/
theorem p10QM_faceOf_alpha_of_mem {f : M.Face} (bf : FaceBoundary M f) {l : List M.Dart}
    (hl : ∀ e ∈ l, e ∈ bf.darts) {d : M.Dart} (hd : d ∈ l.reverse.map M.alpha) :
    M.faceOf (M.alpha d) = f := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
  rw [M.alpha_involutive e]
  exact (bf.mem_iff e).mp (hl e (List.mem_reverse.mp he))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QM_faceOf_alpha_of_mem

/-- The darts of the two arcs of the split are on `c`, with reverses on `s` and on `o`. -/
theorem p10QM_arc_facts {F : Finset M.Face} (c : BoundaryCycle M F) {o s : M.Face}
    {bs : FaceBoundary M s} {bo : FaceBoundary M o} (a : CyclicArc bs.darts)
    (b : CyclicArc (bo.darts.reverse.map M.alpha)) {s₁ s₂ : List M.Dart}
    (hsplit : c.cycle = s₁ ++ a.darts.reverse.map M.alpha ++ s₂ ++ b.darts) :
    (∀ d ∈ a.darts.reverse.map M.alpha, d ∈ c.cycle ∧ M.faceOf (M.alpha d) = s) ∧
      ∀ d ∈ b.darts, d ∈ c.cycle ∧ M.faceOf (M.alpha d) = o := by
  refine ⟨fun d hd => ⟨?_, p10QM_faceOf_alpha_of_mem M bs
      (fun e he => a.mem_cycle_of_mem_darts he) hd⟩,
    fun d hd => ⟨?_, p10QM_faceOf_alpha_of_mem M bo (fun e he => he)
      (b.mem_cycle_of_mem_darts hd)⟩⟩
  · rw [hsplit]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hd))
  · rw [hsplit]
    exact List.mem_append_right _ hd

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QM_arc_facts

end Arcs

/-- **Quadrant `p = q = false` for a lobe with the rest of `c` and both `o, s` on its side.** -/
theorem p10QM_move_FF (M : CombMap.{v}) (F : Finset M.Face) (c : BoundaryCycle M F)
    (o s k : M.Face) (bs : FaceBoundary M s) (bo : FaceBoundary M o) (a : CyclicArc bs.darts)
    (b : CyclicArc (bo.darts.reverse.map M.alpha)) (s₁ s₂ B : List M.Dart)
    (hM : M.IsPlanar) (hc : IsClosedDartWalk M c.cycle) (hk : k ∈ F)
    (hsplit : c.cycle = s₁ ++ a.darts.reverse.map M.alpha ++ s₂ ++ b.darts)
    (hblk : p10QM_CyclicBlock c.cycle B) (hB : IsSimpleClosedWalk M B)
    (hP : ∃ d ∈ c.cycle, d ∉ B) (hin : ∀ d ∈ c.cycle, d ∉ B → M.faceOf d ∈ sideFaces M B)
    (ho : o ∈ sideFaces M B) (hs : s ∈ sideFaces M B) :
    ∃ (B : List M.Dart) (p q : Bool), (∀ d ∈ B, d ∈ c.cycle) ∧
      ¬p10FM_InZ M F B p q o ∧ ¬p10FM_InZ M F B p q s ∧ ¬p10FM_InZ M F B p q k ∧
      (∃ y ∈ c.cycle, movePred M (p10FM_z M F B p q) y = false) ∧
      (a.darts.reverse.map M.alpha).filter (movePred M (p10FM_z M F B p q)) <:+:
        a.darts.reverse.map M.alpha ∧
      b.darts.filter (movePred M (p10FM_z M F B p q)) <+: b.darts ∧
      IsClosedDartWalk M (c.cycle.filter (movePred M (p10FM_z M F B p q))) := by
  have hBc := p10QM_cyclicBlock_subset hblk
  obtain ⟨hla, hlb⟩ := p10QM_arc_facts M c a b hsplit
  have hkeep : ∀ d ∈ c.cycle, movePred M (p10FM_z M F B false false) d = true ↔ d ∉ B := by
    intro d hd
    rw [p10QM_movePred_FF M c B hd]
    constructor
    · intro h hdB
      obtain ⟨-, hout⟩ := (hB.isBoundaryDart_sideFaces_iff hM d).mpr hdB
      exact hout h
    · intro hdB
      exact (p10QM_side_alpha_iff M B hdB
        fun h => p10QM_alpha_not_mem M c hd (hBc _ h)).mp (hin d hd hdB)
  have hfa : (a.darts.reverse.map M.alpha).filter (movePred M (p10FM_z M F B false false)) =
      a.darts.reverse.map M.alpha := List.filter_eq_self.mpr fun d hd =>
    (p10QM_movePred_FF M c B (hla d hd).1).mpr (by rw [(hla d hd).2]; exact hs)
  have hfb : b.darts.filter (movePred M (p10FM_z M F B false false)) = b.darts :=
    List.filter_eq_self.mpr fun d hd =>
      (p10QM_movePred_FF M c B (hlb d hd).1).mpr (by rw [(hlb d hd).2]; exact ho)
  refine ⟨B, false, false, hBc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨h, -⟩
    exact Bool.false_ne_true (h.mp ho)
  · rintro ⟨h, -⟩
    exact Bool.false_ne_true (h.mp hs)
  · rintro ⟨-, h⟩
    exact Bool.false_ne_true (h.mp hk)
  · obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil B hB.ne_nil
    exact ⟨y, hBc y hy, Bool.eq_false_iff.mpr fun h => (hkeep y (hBc y hy)).mp h hy⟩
  · rw [hfa]
    exact List.infix_refl _
  · rw [hfb]
    exact List.prefix_refl _
  · exact p10QM_closed_filter_remove hc c.cycle_nodup hblk hB.isClosedDartWalk hP hkeep

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QM_move_FF

/-- **Quadrant `p = true, q = false` for a lobe with the rest of `c` on its side and both `o, s`
off it.** -/
theorem p10QM_move_TF (M : CombMap.{v}) (F : Finset M.Face) (c : BoundaryCycle M F)
    (o s k : M.Face) (bs : FaceBoundary M s) (bo : FaceBoundary M o) (a : CyclicArc bs.darts)
    (b : CyclicArc (bo.darts.reverse.map M.alpha)) (s₁ s₂ B : List M.Dart)
    (hM : M.IsPlanar) (hk : k ∈ F)
    (hsplit : c.cycle = s₁ ++ a.darts.reverse.map M.alpha ++ s₂ ++ b.darts)
    (hblk : p10QM_CyclicBlock c.cycle B) (hB : IsSimpleClosedWalk M B)
    (hP : ∃ d ∈ c.cycle, d ∉ B) (hin : ∀ d ∈ c.cycle, d ∉ B → M.faceOf d ∈ sideFaces M B)
    (ho : o ∉ sideFaces M B) (hs : s ∉ sideFaces M B) :
    ∃ (B : List M.Dart) (p q : Bool), (∀ d ∈ B, d ∈ c.cycle) ∧
      ¬p10FM_InZ M F B p q o ∧ ¬p10FM_InZ M F B p q s ∧ ¬p10FM_InZ M F B p q k ∧
      (∃ y ∈ c.cycle, movePred M (p10FM_z M F B p q) y = false) ∧
      (a.darts.reverse.map M.alpha).filter (movePred M (p10FM_z M F B p q)) <:+:
        a.darts.reverse.map M.alpha ∧
      b.darts.filter (movePred M (p10FM_z M F B p q)) <+: b.darts ∧
      IsClosedDartWalk M (c.cycle.filter (movePred M (p10FM_z M F B p q))) := by
  have hBc := p10QM_cyclicBlock_subset hblk
  obtain ⟨hla, hlb⟩ := p10QM_arc_facts M c a b hsplit
  have hkeep : ∀ d ∈ c.cycle, movePred M (p10FM_z M F B true false) d = true ↔ d ∈ B := by
    intro d hd
    rw [p10QM_movePred_TF M c B hd]
    constructor
    · intro h
      by_contra hdB
      exact h ((p10QM_side_alpha_iff M B hdB
        fun h' => p10QM_alpha_not_mem M c hd (hBc _ h')).mp (hin d hd hdB))
    · intro hdB
      obtain ⟨-, hout⟩ := (hB.isBoundaryDart_sideFaces_iff hM d).mpr hdB
      exact hout
  have hfa : (a.darts.reverse.map M.alpha).filter (movePred M (p10FM_z M F B true false)) =
      a.darts.reverse.map M.alpha := List.filter_eq_self.mpr fun d hd =>
    (p10QM_movePred_TF M c B (hla d hd).1).mpr (by rw [(hla d hd).2]; exact hs)
  have hfb : b.darts.filter (movePred M (p10FM_z M F B true false)) = b.darts :=
    List.filter_eq_self.mpr fun d hd =>
      (p10QM_movePred_TF M c B (hlb d hd).1).mpr (by rw [(hlb d hd).2]; exact ho)
  refine ⟨B, true, false, hBc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨h, -⟩
    exact ho (h.mpr rfl)
  · rintro ⟨h, -⟩
    exact hs (h.mpr rfl)
  · rintro ⟨-, h⟩
    exact Bool.false_ne_true (h.mp hk)
  · obtain ⟨y, hy, hyB⟩ := hP
    exact ⟨y, hy, Bool.eq_false_iff.mpr fun h => hyB ((hkeep y hy).mp h)⟩
  · rw [hfa]
    exact List.infix_refl _
  · rw [hfb]
    exact List.prefix_refl _
  · exact p10QM_closed_filter_keep c.cycle_nodup hblk hB.isClosedDartWalk hkeep

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QM_move_TF

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove
