import GroupApproximation.GGT.VanKampen.ClosedWalkPinchSplit
import GroupApproximation.Meta.AxiomGuard

/-!
# Filtering a closed walk whose keep predicate only switches at one vertex

Lane gl-p10-93.  Helper lemmas for `P10FilterMoveExists.p10FM_QuadrantMoveStatement`.

Let `w` be a closed dart walk and `pr` a keep predicate.  Suppose that whenever two darts
`d, e ∈ w` with `alpha d` ending where `e` starts (a possible consecutive pair) have different
`pr`-values, `e` starts at one fixed vertex `v0`.  Then the kept darts `w.filter pr` still form
a closed dart walk, as soon as one dart is kept (`p10QS_closed_filter_of_switch`).

Route.  A walk from `u` to `u'` is encoded by the recursive predicate `p10QS_Walk`
(`p10QS_walk_cons_iff` converts it to a chain plus endpoint).  `p10QS_SW b L` says that every
switch of `pr` along `L`, starting from status `b`, happens at `v0`.  By induction
(`p10QS_walk_filter`), `L.filter pr` is a walk from `u` (or `v0`, if the status is `false`) to
`u'` (or `v0`, if the final status is `false`).  Starting from the status of the last dart makes
both ends equal (`p10QS_last_cons`), which gives a closed walk.

All PROVED.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove

universe v

section Switch

variable {α β : Type*}

/-- `p10QS_Walk st en u L u'`: the list `L` is a walk from `u` to `u'`, where each item `x`
starts at `st x` and ends at `en x`. -/
def p10QS_Walk (st en : α → β) : β → List α → β → Prop
  | u, [], u' => u = u'
  | u, x :: L, u' => st x = u ∧ p10QS_Walk st en (en x) L u'

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QS_Walk

/-- `p10QS_SW st pr v0 b L`: along `L`, starting from status `b`, every switch of `pr` happens at
an item starting at `v0`. -/
def p10QS_SW (st : α → β) (pr : α → Bool) (v0 : β) : Bool → List α → Prop
  | _, [] => True
  | b, x :: L => (pr x ≠ b → st x = v0) ∧ p10QS_SW st pr v0 (pr x) L

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QS_SW

/-- The status after running through `L`: the `pr`-value of its last item, or `b` if empty. -/
def p10QS_last (pr : α → Bool) : Bool → List α → Bool
  | b, [] => b
  | _, x :: L => p10QS_last pr (pr x) L

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QS_last

theorem p10QS_last_cons (pr : α → Bool) (b : Bool) (x : α) (L : List α) :
    p10QS_last pr b (x :: L) = pr ((x :: L).getLast (List.cons_ne_nil x L)) := by
  induction L generalizing b x with
  | nil => rfl
  | cons y L ih =>
    show p10QS_last pr (pr x) (y :: L) = _
    simp only [ih, List.getLast_cons_cons]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QS_last_cons

/-- A walk on a nonempty list is a chain with the right endpoints. -/
theorem p10QS_walk_cons_iff (st en : α → β) (u u' : β) (x : α) (L : List α) :
    p10QS_Walk st en u (x :: L) u' ↔ st x = u ∧ (x :: L).IsChain (fun d e => en d = st e) ∧
      en ((x :: L).getLast (List.cons_ne_nil x L)) = u' := by
  induction L generalizing u x with
  | nil =>
    show st x = u ∧ en x = u' ↔ st x = u ∧ [x].IsChain _ ∧ en x = u'
    exact ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, List.IsChain.singleton x, h₂⟩, fun ⟨h₁, _, h₂⟩ => ⟨h₁, h₂⟩⟩
  | cons y L ih =>
    show st x = u ∧ p10QS_Walk st en (en x) (y :: L) u' ↔ _
    rw [ih, List.isChain_cons_cons, List.getLast_cons_cons]
    constructor
    · rintro ⟨h₁, h₂, h₃, h₄⟩
      exact ⟨h₁, ⟨h₂.symm, h₃⟩, h₄⟩
    · rintro ⟨h₁, ⟨h₂, h₃⟩, h₄⟩
      exact ⟨h₁, h₂.symm, h₃, h₄⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QS_walk_cons_iff

/-- **The kept items of a walk switching only at `v0` form a walk.** -/
theorem p10QS_walk_filter (st en : α → β) (pr : α → Bool) (v0 : β) (L : List α) :
    ∀ (b : Bool) (u u' : β), p10QS_Walk st en u L u' → p10QS_SW st pr v0 b L →
      p10QS_Walk st en (cond b u v0) (L.filter pr) (cond (p10QS_last pr b L) u' v0) := by
  induction L with
  | nil =>
    intro b u u' hw _
    have h : u = u' := hw
    subst h
    exact rfl
  | cons x L ih =>
    intro b u u' hw hs
    obtain ⟨hx, hw'⟩ : st x = u ∧ p10QS_Walk st en (en x) L u' := hw
    obtain ⟨hsw, hs'⟩ : (pr x ≠ b → st x = v0) ∧ p10QS_SW st pr v0 (pr x) L := hs
    have ih' := ih (pr x) (en x) u' hw' hs'
    have hl : p10QS_last pr b (x :: L) = p10QS_last pr (pr x) L := rfl
    rw [hl]
    rcases Bool.eq_false_or_eq_true (pr x) with hpx | hpx
    · rw [hpx] at ih' hsw
      rw [hpx, List.filter_cons_of_pos (p := pr) (a := x) (l := L) hpx]
      show st x = cond b u v0 ∧
        p10QS_Walk st en (en x) (L.filter pr) (cond (p10QS_last pr true L) u' v0)
      refine ⟨?_, ih'⟩
      cases b
      · exact hsw (by decide)
      · exact hx
    · rw [hpx] at ih' hsw
      rw [hpx, List.filter_cons_of_neg (p := pr) (a := x) (l := L) (by simp [hpx])]
      have hb : cond b u v0 = v0 := by
        cases b
        · rfl
        · exact hx.symm.trans (hsw (by decide))
      rw [hb]
      exact ih'

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QS_walk_filter

/-- If every possible consecutive pair with a switch of `pr` meets at `v0`, every walk inside `w`
switches only at `v0`. -/
theorem p10QS_sw_of_pairs (st en : α → β) (pr : α → Bool) (v0 : β) (w : List α)
    (hpair : ∀ d ∈ w, ∀ e ∈ w, en d = st e → pr d ≠ pr e → st e = v0) (L : List α) :
    ∀ (p : α) (u' : β), p ∈ w → (∀ x ∈ L, x ∈ w) → p10QS_Walk st en (en p) L u' →
      p10QS_SW st pr v0 (pr p) L := by
  induction L with
  | nil =>
    intro _ _ _ _ _
    exact True.intro
  | cons x L ih =>
    intro p u' hp hL hw
    obtain ⟨hx, hw'⟩ : st x = en p ∧ p10QS_Walk st en (en x) L u' := hw
    have hxw : x ∈ w := hL x List.mem_cons_self
    show (pr x ≠ pr p → st x = v0) ∧ p10QS_SW st pr v0 (pr x) L
    exact ⟨fun hne => hpair p hp x hxw hx.symm (Ne.symm hne),
      ih x u' hxw (fun y hy => hL y (List.mem_cons_of_mem x hy)) hw'⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QS_sw_of_pairs

/-- **A closed walk switching only at `v0` filters to a walk with equal ends.** -/
theorem p10QS_walk_filter_closed (st en : α → β) (pr : α → Bool) (v0 : β) (x : α) (L : List α)
    (hc : (x :: L).IsChain (fun d e => en d = st e))
    (hcl : en ((x :: L).getLast (List.cons_ne_nil x L)) = st x)
    (hpair : ∀ d ∈ x :: L, ∀ e ∈ x :: L, en d = st e → pr d ≠ pr e → st e = v0) :
    ∃ U : β, p10QS_Walk st en U ((x :: L).filter pr) U := by
  obtain ⟨p, hpdef⟩ : ∃ p, p = (x :: L).getLast (List.cons_ne_nil x L) := ⟨_, rfl⟩
  have hp : p ∈ x :: L := by
    rw [hpdef]
    exact List.getLast_mem _
  rw [← hpdef] at hcl
  have hw : p10QS_Walk st en (en p) (x :: L) (en p) :=
    (p10QS_walk_cons_iff st en (en p) (en p) x L).mpr ⟨hcl.symm, hc, by rw [← hpdef]⟩
  have hsw := p10QS_sw_of_pairs st en pr v0 (x :: L) hpair (x :: L) p (en p) hp
    (fun y hy => hy) hw
  have hf := p10QS_walk_filter st en pr v0 (x :: L) (pr p) (en p) (en p) hw hsw
  rw [p10QS_last_cons, ← hpdef] at hf
  exact ⟨_, hf⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QS_walk_filter_closed

end Switch

/-- **Filtering a closed dart walk whose keep predicate switches only at `v0`.**  If two darts
`d, e ∈ w` with `alpha d` ending at the start of `e` and different `pr`-values always meet at
`v0`, and some dart is kept, then the kept darts form a closed dart walk. -/
theorem p10QS_closed_filter_of_switch {M : CombMap.{v}} {w : List M.Dart} (pr : M.Dart → Bool)
    (v0 : M.Vertex) (hw : IsClosedDartWalk M w)
    (hpair : ∀ d ∈ w, ∀ e ∈ w, M.vertexOf (M.alpha d) = M.vertexOf e → pr d ≠ pr e →
      M.vertexOf e = v0)
    (hkept : ∃ d ∈ w, pr d = true) : IsClosedDartWalk M (w.filter pr) := by
  obtain ⟨hne, hc, hcl⟩ := hw
  obtain ⟨x, L, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨U, hU⟩ := p10QS_walk_filter_closed M.vertexOf (fun d => M.vertexOf (M.alpha d)) pr v0
    x L hc hcl hpair
  obtain ⟨d, hd, hpd⟩ := hkept
  have hfne : (x :: L).filter pr ≠ [] := List.ne_nil_of_mem (List.mem_filter.mpr ⟨hd, hpd⟩)
  obtain ⟨y, L₂, hyL⟩ := List.exists_cons_of_ne_nil hfne
  rw [hyL] at hU ⊢
  obtain ⟨h₁, h₂, h₃⟩ :=
    (p10QS_walk_cons_iff M.vertexOf (fun d => M.vertexOf (M.alpha d)) U U y L₂).mp hU
  exact ⟨List.cons_ne_nil y L₂, h₂, h₃.trans h₁.symm⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QS_closed_filter_of_switch

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove
