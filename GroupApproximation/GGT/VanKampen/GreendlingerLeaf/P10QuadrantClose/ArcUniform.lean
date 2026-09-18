import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.Inside
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantSelect.MoveCut
import GroupApproximation.Meta.AxiomGuard

/-!
# Arcs off the lobe are kept all-or-nothing

Lane gl-p10-95.  Helper theorems for `P10FilterMoveExists.p10FM_QuadrantMoveStatement`.

When a simple closed walk `B ⊆ c` meets neither arc of the split
`c = s₁ ++ a⁻¹ ++ s₂ ++ b`, every dart of `a⁻¹` has `faceOf (alpha d) = s`. It is off `B`, and so
is its reverse, because `alpha d ∉ c`. So its face is on the side of `B` exactly when `s` is,
and every quadrant move keeps all of `a⁻¹` or none of it (likewise `b` with `o`).  Hence the two
arc clauses of the statement hold for EVERY quadrant `p q`.  This discharges the hypotheses
`hfa`/`hfb` of the untouched-lobe moves `p10QS_move_untouched_TT/_FT` when the arcs avoid `B`.

* `p10QC_filter_infix_of_uniform`, `p10QC_filter_prefix_of_uniform`: pure list facts.
* `p10QC_movePred_of_alpha_face`: the keep rule off `B` through the reverse dart's face.
* `p10QC_uniform_of_face`: a list of such darts with a common reverse face is kept uniformly.
* `p10QC_arc_filters`: both arc clauses, for all `p q`, from the arcs avoiding `B`.
* `p10QC_move_untouched_TT_arcsOff`, `p10QC_move_untouched_FT_arcsOff`: the full
  conclusion for an untouched lobe that avoids both arcs and has a dart off its side.

All PROVED.  They do not use the rose premises.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove

universe u v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10FilterMoveExists

/-- A filter that keeps all of `l` or none of it is an infix of `l`. -/
theorem p10QC_filter_infix_of_uniform {α : Type u} (l : List α) (P : α → Bool)
    (h : (∀ x ∈ l, P x = true) ∨ ∀ x ∈ l, P x = false) : l.filter P <:+: l := by
  rcases h with h | h
  · have h1 : l.filter P = l := List.filter_eq_self.mpr h
    exact (congrArg (fun x => x <:+: l) h1).mpr (List.infix_refl l)
  · have h0 : l.filter P = [] := List.filter_eq_nil_iff.mpr fun x hx => by
      rw [h x hx]
      exact Bool.false_ne_true
    rw [h0]
    exact List.nil_infix

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QC_filter_infix_of_uniform

/-- A filter that keeps all of `l` or none of it is a prefix of `l`. -/
theorem p10QC_filter_prefix_of_uniform {α : Type u} (l : List α) (P : α → Bool)
    (h : (∀ x ∈ l, P x = true) ∨ ∀ x ∈ l, P x = false) : l.filter P <+: l := by
  rcases h with h | h
  · have h1 : l.filter P = l := List.filter_eq_self.mpr h
    exact (congrArg (fun x => x <+: l) h1).mpr (List.prefix_refl l)
  · have h0 : l.filter P = [] := List.filter_eq_nil_iff.mpr fun x hx => by
      rw [h x hx]
      exact Bool.false_ne_true
    rw [h0]
    exact List.nil_prefix

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QC_filter_prefix_of_uniform

section ArcUniform

variable (M : CombMap.{v})

/-- **Keep rule off `B` through the reverse face.** A dart `d` of `c` off `B`, whose reverse lies
in face `f`, is kept by the quadrant move `p q` iff `f` is on the side of `B` exactly when
`p = false`. -/
theorem p10QC_movePred_of_alpha_face {F : Finset M.Face} (c : BoundaryCycle M F)
    {B : List M.Dart} (hBc : ∀ e ∈ B, e ∈ c.cycle) (p q : Bool) {f : M.Face} {d : M.Dart}
    (hd : d ∈ c.cycle) (hdB : d ∉ B) (hf : M.faceOf (M.alpha d) = f) :
    movePred M (p10FM_z M F B p q) d = true ↔ (f ∈ sideFaces M B ↔ p = false) := by
  subst hf
  rw [p10QS_movePred_off M c hBc p q hd hdB,
    p10QM_side_alpha_iff M B hdB fun h => p10QM_alpha_not_mem M c hd (hBc _ h)]

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QC_movePred_of_alpha_face

/-- **Uniform keep.** Darts of `c` off `B` whose reverses share a face are kept by a quadrant
move all together or not at all. -/
theorem p10QC_uniform_of_face {F : Finset M.Face} (c : BoundaryCycle M F) {B : List M.Dart}
    (hBc : ∀ e ∈ B, e ∈ c.cycle) (p q : Bool) {f : M.Face} {l : List M.Dart}
    (hl : ∀ d ∈ l, d ∈ c.cycle ∧ M.faceOf (M.alpha d) = f) (hlB : ∀ d ∈ l, d ∉ B) :
    (∀ d ∈ l, movePred M (p10FM_z M F B p q) d = true) ∨
      ∀ d ∈ l, movePred M (p10FM_z M F B p q) d = false := by
  by_cases hfp : (f ∈ sideFaces M B ↔ p = false)
  · exact Or.inl fun d hd =>
      (p10QC_movePred_of_alpha_face M c hBc p q (hl d hd).1 (hlB d hd) (hl d hd).2).mpr hfp
  · exact Or.inr fun d hd => Bool.eq_false_iff.mpr fun h =>
      hfp ((p10QC_movePred_of_alpha_face M c hBc p q (hl d hd).1 (hlB d hd) (hl d hd).2).mp h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QC_uniform_of_face

/-- **Both arc clauses for every quadrant**, when `B ⊆ c` avoids both arcs of the split. -/
theorem p10QC_arc_filters {F : Finset M.Face} (c : BoundaryCycle M F) {o s : M.Face}
    {bs : FaceBoundary M s} {bo : FaceBoundary M o} (a : CyclicArc bs.darts)
    (b : CyclicArc (bo.darts.reverse.map M.alpha)) {s₁ s₂ : List M.Dart}
    (hsplit : c.cycle = s₁ ++ a.darts.reverse.map M.alpha ++ s₂ ++ b.darts)
    {B : List M.Dart} (hBc : ∀ e ∈ B, e ∈ c.cycle) (p q : Bool)
    (hla : ∀ d ∈ a.darts.reverse.map M.alpha, d ∉ B) (hlb : ∀ d ∈ b.darts, d ∉ B) :
    (a.darts.reverse.map M.alpha).filter (movePred M (p10FM_z M F B p q)) <:+:
        a.darts.reverse.map M.alpha ∧
      b.darts.filter (movePred M (p10FM_z M F B p q)) <+: b.darts := by
  obtain ⟨ha, hb⟩ := p10QM_arc_facts M c a b hsplit
  exact ⟨p10QC_filter_infix_of_uniform _ _ (p10QC_uniform_of_face M c hBc p q ha hla),
    p10QC_filter_prefix_of_uniform _ _ (p10QC_uniform_of_face M c hBc p q hb hlb)⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QC_arc_filters

end ArcUniform

section MoveArcsOff

/-- **Quadrant `p = q = true` for an untouched lobe that avoids both arcs**, with `k` off its
side and some dart of `c` off `B` whose face is off the side. -/
theorem p10QC_move_untouched_TT_arcsOff (M : CombMap.{v}) (F : Finset M.Face)
    (c : BoundaryCycle M F) (o s k : M.Face) (bs : FaceBoundary M s) (bo : FaceBoundary M o)
    (a : CyclicArc bs.darts) (b : CyclicArc (bo.darts.reverse.map M.alpha))
    (s₁ s₂ : List M.Dart) (B : List M.Dart) (hM : M.IsPlanar) (hc : IsClosedDartWalk M c.cycle)
    (hsplit : c.cycle = s₁ ++ a.darts.reverse.map M.alpha ++ s₂ ++ b.darts)
    (hB : IsSimpleClosedWalk M B) (hBc : ∀ e ∈ B, e ∈ c.cycle) {v0 : M.Vertex}
    (hU : p10QS_Untouched M c.cycle B v0)
    (hPout : ∃ d ∈ c.cycle, d ∉ B ∧ M.faceOf d ∉ sideFaces M B)
    (ho : o ∉ F) (hs : s ∉ F) (hk : k ∉ sideFaces M B)
    (hla : ∀ d ∈ a.darts.reverse.map M.alpha, d ∉ B) (hlb : ∀ d ∈ b.darts, d ∉ B) :
    ∃ (B : List M.Dart) (p q : Bool), (∀ d ∈ B, d ∈ c.cycle) ∧
      ¬p10FM_InZ M F B p q o ∧ ¬p10FM_InZ M F B p q s ∧ ¬p10FM_InZ M F B p q k ∧
      (∃ y ∈ c.cycle, movePred M (p10FM_z M F B p q) y = false) ∧
      (a.darts.reverse.map M.alpha).filter (movePred M (p10FM_z M F B p q)) <:+:
        a.darts.reverse.map M.alpha ∧
      b.darts.filter (movePred M (p10FM_z M F B p q)) <+: b.darts ∧
      IsClosedDartWalk M (c.cycle.filter (movePred M (p10FM_z M F B p q))) := by
  obtain ⟨hfa, hfb⟩ := p10QC_arc_filters M c a b hsplit hBc true true hla hlb
  exact p10QS_move_untouched_TT M F c o s k bs bo a b B hM hc hB hBc hU hPout ho hs hk hfa hfb

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QC_move_untouched_TT_arcsOff

/-- **Quadrant `p = false, q = true` for an untouched lobe that avoids both arcs**, with `k` on
its side and some dart of `c` off `B` whose face is off the side. -/
theorem p10QC_move_untouched_FT_arcsOff (M : CombMap.{v}) (F : Finset M.Face)
    (c : BoundaryCycle M F) (o s k : M.Face) (bs : FaceBoundary M s) (bo : FaceBoundary M o)
    (a : CyclicArc bs.darts) (b : CyclicArc (bo.darts.reverse.map M.alpha))
    (s₁ s₂ : List M.Dart) (B : List M.Dart) (hM : M.IsPlanar) (hc : IsClosedDartWalk M c.cycle)
    (hsplit : c.cycle = s₁ ++ a.darts.reverse.map M.alpha ++ s₂ ++ b.darts)
    (hB : IsSimpleClosedWalk M B) (hBc : ∀ e ∈ B, e ∈ c.cycle) {v0 : M.Vertex}
    (hU : p10QS_Untouched M c.cycle B v0)
    (hPout : ∃ d ∈ c.cycle, d ∉ B ∧ M.faceOf d ∉ sideFaces M B)
    (ho : o ∉ F) (hs : s ∉ F) (hk : k ∈ sideFaces M B)
    (hla : ∀ d ∈ a.darts.reverse.map M.alpha, d ∉ B) (hlb : ∀ d ∈ b.darts, d ∉ B) :
    ∃ (B : List M.Dart) (p q : Bool), (∀ d ∈ B, d ∈ c.cycle) ∧
      ¬p10FM_InZ M F B p q o ∧ ¬p10FM_InZ M F B p q s ∧ ¬p10FM_InZ M F B p q k ∧
      (∃ y ∈ c.cycle, movePred M (p10FM_z M F B p q) y = false) ∧
      (a.darts.reverse.map M.alpha).filter (movePred M (p10FM_z M F B p q)) <:+:
        a.darts.reverse.map M.alpha ∧
      b.darts.filter (movePred M (p10FM_z M F B p q)) <+: b.darts ∧
      IsClosedDartWalk M (c.cycle.filter (movePred M (p10FM_z M F B p q))) := by
  obtain ⟨hfa, hfb⟩ := p10QC_arc_filters M c a b hsplit hBc false true hla hlb
  exact p10QS_move_untouched_FT M F c o s k bs bo a b B hM hc hB hBc hU hPout ho hs hk hfa hfb

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QC_move_untouched_FT_arcsOff

end MoveArcsOff

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove
