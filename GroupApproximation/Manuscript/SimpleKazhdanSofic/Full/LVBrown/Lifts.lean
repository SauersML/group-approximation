import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVBrown.Macbeath
import GroupApproximation.Meta.AxiomGuard

/-!
# Lifting edge paths to the Brown group, and homotopy invariance (T1d)

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735, leaf **T1d** (Brown 1984, Thm 1;
Macbeath 1964).  This file builds on `LVBrown/Macbeath.lean`.

A *state* is a pair `s = (π, y) : D.Pres × V`.  Its position is `D.pos s = toG π • y`.
`D.Lifts p s s'` says that the edge path `p` lifts from the state `s` to the state `s'` through
covering steps `D.R`.  Lifts can be saturated at both ends.  They split along concatenation.
They are invariant under backtracking and under passage across an ordered triangle, hence under
combinatorial homotopy (`lifts_iff_of_homotopic`).  Every path lifts (`exists_lifts`).
-/

namespace GroupApproximation.Full.LVBrown

open GroupApproximation.Full.LVFrame
open GroupApproximation.Full.LVFrame.OrderedTwoComplex

universe u

variable {V : Type u} {X : OrderedTwoComplex V} {G : Type*} [Group G] [MulAction G V]

namespace Datum

variable (D : Datum X G)

/-- States of the covering: an element of the Brown group and a vertex. -/
abbrev State : Type _ := D.Pres × V

/-- The position `toG π • y` of a state `(π, y)`. -/
abbrev pos (s : D.State) : V := D.toG s.1 • s.2

/-- The covering relation on states. -/
abbrev R (s s' : D.State) : Prop := D.Rel s.1 s.2 s'.1 s'.2

/-- Related states have near positions. -/
theorem rel_near_pos {s s' : D.State} (h : D.R s s') : Near X (D.pos s) (D.pos s') := by
  obtain ⟨-, -, t, ht, hn⟩ := h
  have e : D.pos s' = D.toG s.1 • t.1 • s'.2 := by
    show D.toG s'.1 • s'.2 = D.toG s.1 • t.1 • s'.2
    rw [ht, map_mul, D.toG_of, mul_smul]
  rw [e]
  exact Near.smul D.action (D.toG s.1) hn

/-- `D.Lifts p s s'`: the edge path `p` lifts from the state `s` to the state `s'`. -/
def Lifts : {a c : V} → X.EdgePath a c → D.State → D.State → Prop
  | _, _, .nil v, s, s' => D.pos s = v ∧ D.R s s' ∧ D.pos s' = v
  | a, _, .fwd _ p, s, s' => D.pos s = a ∧ ∃ n : D.State, D.R s n ∧ Lifts p n s'
  | a, _, .bwd _ p, s, s' => D.pos s = a ∧ ∃ n : D.State, D.R s n ∧ Lifts p n s'

theorem lifts_nil (v : V) (s s' : D.State) :
    D.Lifts (EdgePath.nil v) s s' ↔ D.pos s = v ∧ D.R s s' ∧ D.pos s' = v := Iff.rfl

theorem lifts_fwd {a b c : V} (e : X.edge a b) (p : X.EdgePath b c) (s s' : D.State) :
    D.Lifts (EdgePath.fwd e p) s s' ↔ D.pos s = a ∧ ∃ n : D.State, D.R s n ∧ D.Lifts p n s' :=
  Iff.rfl

theorem lifts_bwd {a b c : V} (e : X.edge b a) (p : X.EdgePath b c) (s s' : D.State) :
    D.Lifts (EdgePath.bwd e p) s s' ↔ D.pos s = a ∧ ∃ n : D.State, D.R s n ∧ D.Lifts p n s' :=
  Iff.rfl

/-- The end states of a lift lie over the endpoints of the path. -/
theorem lifts_ends : ∀ {a c : V} (p : X.EdgePath a c) {s s' : D.State}, D.Lifts p s s' →
    s.2 ∈ D.F ∧ D.pos s = a ∧ s'.2 ∈ D.F ∧ D.pos s' = c := by
  intro a c p
  induction p with
  | nil v =>
    intro s s' h
    obtain ⟨h1, h2, h3⟩ := (D.lifts_nil v s s').mp h
    exact ⟨h2.1, h1, h2.2.1, h3⟩
  | fwd e p ih =>
    intro s s' h
    obtain ⟨h1, n, hn, hp⟩ := (D.lifts_fwd e p s s').mp h
    obtain ⟨-, -, h4, h5⟩ := ih hp
    exact ⟨hn.1, h1, h4, h5⟩
  | bwd e p ih =>
    intro s s' h
    obtain ⟨h1, n, hn, hp⟩ := (D.lifts_bwd e p s s').mp h
    obtain ⟨-, -, h4, h5⟩ := ih hp
    exact ⟨hn.1, h1, h4, h5⟩

/-- Saturation at the start. -/
theorem lifts_of_start {a c : V} (p : X.EdgePath a c) {s₀ s₁ s' : D.State} (h₀₁ : D.R s₀ s₁)
    (hpos : D.pos s₀ = D.pos s₁) (h : D.Lifts p s₁ s') : D.Lifts p s₀ s' := by
  cases p with
  | nil _ =>
    obtain ⟨h1, h2, h3⟩ := (D.lifts_nil _ s₁ s').mp h
    exact (D.lifts_nil _ s₀ s').mpr
      ⟨hpos.trans h1, D.rel_trans_of_pos_eq_left h₀₁ h2 hpos, h3⟩
  | fwd e q =>
    obtain ⟨h1, n, hn, hq⟩ := (D.lifts_fwd e q s₁ s').mp h
    exact (D.lifts_fwd e q s₀ s').mpr
      ⟨hpos.trans h1, n, D.rel_trans_of_pos_eq_left h₀₁ hn hpos, hq⟩
  | bwd e q =>
    obtain ⟨h1, n, hn, hq⟩ := (D.lifts_bwd e q s₁ s').mp h
    exact (D.lifts_bwd e q s₀ s').mpr
      ⟨hpos.trans h1, n, D.rel_trans_of_pos_eq_left h₀₁ hn hpos, hq⟩

/-- Saturation at the end. -/
theorem lifts_of_end : ∀ {a c : V} (p : X.EdgePath a c) {s s₁ s₂ : D.State},
    D.Lifts p s s₁ → D.R s₁ s₂ → D.pos s₁ = D.pos s₂ → D.Lifts p s s₂ := by
  intro a c p
  induction p with
  | nil v =>
    intro s s₁ s₂ h h₁₂ hpos
    obtain ⟨h1, h2, h3⟩ := (D.lifts_nil v s s₁).mp h
    exact (D.lifts_nil v s s₂).mpr
      ⟨h1, D.rel_trans_of_pos_eq_right h2 h₁₂ hpos, hpos.symm.trans h3⟩
  | fwd e p ih =>
    intro s s₁ s₂ h h₁₂ hpos
    obtain ⟨h1, n, hn, hp⟩ := (D.lifts_fwd e p s s₁).mp h
    exact (D.lifts_fwd e p s s₂).mpr ⟨h1, n, hn, ih hp h₁₂ hpos⟩
  | bwd e p ih =>
    intro s s₁ s₂ h h₁₂ hpos
    obtain ⟨h1, n, hn, hp⟩ := (D.lifts_bwd e p s s₁).mp h
    exact (D.lifts_bwd e p s s₂).mpr ⟨h1, n, hn, ih hp h₁₂ hpos⟩

/-- Lifts split along concatenation of paths. -/
theorem lifts_append : ∀ {a b : V} (p : X.EdgePath a b) {c : V} (q : X.EdgePath b c)
    (s s' : D.State), D.Lifts (p.append q) s s' ↔ ∃ m : D.State, D.Lifts p s m ∧ D.Lifts q m s' := by
  intro a b p
  induction p with
  | nil v =>
    intro c q s s'
    rw [EdgePath.nil_append]
    constructor
    · intro h
      obtain ⟨hs, hpos, -, -⟩ := D.lifts_ends q h
      exact ⟨s, (D.lifts_nil v s s).mpr ⟨hpos, D.rel_refl s.1 hs, hpos⟩, h⟩
    · rintro ⟨m, hm, hq⟩
      obtain ⟨h1, h2, h3⟩ := (D.lifts_nil v s m).mp hm
      exact D.lifts_of_start q h2 (h1.trans h3.symm) hq
  | fwd e p ih =>
    intro c q s s'
    rw [EdgePath.fwd_append, D.lifts_fwd e (p.append q) s s']
    constructor
    · rintro ⟨h1, n, hn, hpq⟩
      obtain ⟨m, hm, hq⟩ := (ih q n s').mp hpq
      exact ⟨m, (D.lifts_fwd e p s m).mpr ⟨h1, n, hn, hm⟩, hq⟩
    · rintro ⟨m, hm, hq⟩
      obtain ⟨h1, n, hn, hp⟩ := (D.lifts_fwd e p s m).mp hm
      exact ⟨h1, n, hn, (ih q n s').mpr ⟨m, hp, hq⟩⟩
  | bwd e p ih =>
    intro c q s s'
    rw [EdgePath.bwd_append, D.lifts_bwd e (p.append q) s s']
    constructor
    · rintro ⟨h1, n, hn, hpq⟩
      obtain ⟨m, hm, hq⟩ := (ih q n s').mp hpq
      exact ⟨m, (D.lifts_bwd e p s m).mpr ⟨h1, n, hn, hm⟩, hq⟩
    · rintro ⟨m, hm, hq⟩
      obtain ⟨h1, n, hn, hp⟩ := (D.lifts_bwd e p s m).mp hm
      exact ⟨h1, n, hn, (ih q n s').mpr ⟨m, hp, hq⟩⟩

/-- Every edge path lifts from every state over its start. -/
theorem exists_lifts : ∀ {a c : V} (p : X.EdgePath a c) (s : D.State), s.2 ∈ D.F →
    D.pos s = a → ∃ s' : D.State, D.Lifts p s s' := by
  intro a c p
  induction p with
  | nil v =>
    intro s hs hpos
    exact ⟨s, (D.lifts_nil v s s).mpr ⟨hpos, D.rel_refl s.1 hs, hpos⟩⟩
  | fwd e p ih =>
    intro s hs hpos
    have hn := Near.of_edge e
    rw [← hpos] at hn
    obtain ⟨π', y', hrel, hpos'⟩ := D.exists_rel hs hn
    obtain ⟨s', hs'⟩ := ih (π', y') hrel.2.1 hpos'
    exact ⟨s', (D.lifts_fwd e p s s').mpr ⟨hpos, (π', y'), hrel, hs'⟩⟩
  | bwd e p ih =>
    intro s hs hpos
    have hn := (Near.of_edge e).symm
    rw [← hpos] at hn
    obtain ⟨π', y', hrel, hpos'⟩ := D.exists_rel hs hn
    obtain ⟨s', hs'⟩ := ih (π', y') hrel.2.1 hpos'
    exact ⟨s', (D.lifts_bwd e p s s').mpr ⟨hpos, (π', y'), hrel, hs'⟩⟩

theorem lifts_backtrack_fwd {b c d : V} (e : X.edge b c) (q : X.EdgePath b d)
    (s s' : D.State) : D.Lifts (EdgePath.fwd e (EdgePath.bwd e q)) s s' ↔ D.Lifts q s s' := by
  rw [D.lifts_fwd e (EdgePath.bwd e q) s s']
  constructor
  · rintro ⟨h1, n, hn, h2⟩
    obtain ⟨-, k, hk, hq⟩ := (D.lifts_bwd e q n s').mp h2
    obtain ⟨-, hkpos, -, -⟩ := D.lifts_ends q hq
    exact D.lifts_of_start q (D.rel_of_fork (Rel.symm D hn) hk (h1.trans hkpos.symm))
      (h1.trans hkpos.symm) hq
  · intro h
    obtain ⟨hs, hpos, -, -⟩ := D.lifts_ends q h
    have hn := Near.of_edge e
    rw [← hpos] at hn
    obtain ⟨π', y', hrel, hpos'⟩ := D.exists_rel hs hn
    exact ⟨hpos, (π', y'), hrel,
      (D.lifts_bwd e q (π', y') s').mpr ⟨hpos', s, Rel.symm D hrel, h⟩⟩

theorem lifts_backtrack_bwd {b c d : V} (e : X.edge c b) (q : X.EdgePath b d)
    (s s' : D.State) : D.Lifts (EdgePath.bwd e (EdgePath.fwd e q)) s s' ↔ D.Lifts q s s' := by
  rw [D.lifts_bwd e (EdgePath.fwd e q) s s']
  constructor
  · rintro ⟨h1, n, hn, h2⟩
    obtain ⟨-, k, hk, hq⟩ := (D.lifts_fwd e q n s').mp h2
    obtain ⟨-, hkpos, -, -⟩ := D.lifts_ends q hq
    exact D.lifts_of_start q (D.rel_of_fork (Rel.symm D hn) hk (h1.trans hkpos.symm))
      (h1.trans hkpos.symm) hq
  · intro h
    obtain ⟨hs, hpos, -, -⟩ := D.lifts_ends q h
    have hn := (Near.of_edge e).symm
    rw [← hpos] at hn
    obtain ⟨π', y', hrel, hpos'⟩ := D.exists_rel hs hn
    exact ⟨hpos, (π', y'), hrel,
      (D.lifts_fwd e q (π', y') s').mpr ⟨hpos', s, Rel.symm D hrel, h⟩⟩

theorem lifts_triangle {b₀ b₁ b₂ d : V} (t : X.tri b₀ b₁ b₂) (q : X.EdgePath b₂ d)
    (s s' : D.State) :
    D.Lifts (EdgePath.fwd (X.tri_edge01 t) (EdgePath.fwd (X.tri_edge12 t) q)) s s' ↔
      D.Lifts (EdgePath.fwd (X.tri_edge02 t) q) s s' := by
  rw [D.lifts_fwd (X.tri_edge01 t) (EdgePath.fwd (X.tri_edge12 t) q) s s',
    D.lifts_fwd (X.tri_edge02 t) q s s']
  constructor
  · rintro ⟨h1, n, hn, h2⟩
    obtain ⟨h3, k, hk, hq⟩ := (D.lifts_fwd (X.tri_edge12 t) q n s').mp h2
    obtain ⟨-, hkpos, -, -⟩ := D.lifts_ends q hq
    refine ⟨h1, k, D.rel_trans_of_tri hn hk ?_, hq⟩
    show X.tri (D.pos s) (D.pos n) (D.pos k)
    rw [h1, h3, hkpos]
    exact t
  · rintro ⟨h1, k, hk, hq⟩
    obtain ⟨-, hkpos, -, -⟩ := D.lifts_ends q hq
    have hn₁ := Near.of_edge (X.tri_edge01 t)
    rw [← h1] at hn₁
    obtain ⟨π₁, y₁, hr₁, hp₁⟩ := D.exists_rel hk.1 hn₁
    have hn₂ := Near.of_edge (X.tri_edge12 t)
    rw [← hp₁] at hn₂
    obtain ⟨π₂, y₂, hr₂, hp₂⟩ := D.exists_rel hr₁.2.1 hn₂
    have hr₀₂ : D.R s (π₂, y₂) := by
      refine D.rel_trans_of_tri hr₁ hr₂ ?_
      show X.tri (D.pos s) (D.toG π₁ • y₁) (D.toG π₂ • y₂)
      rw [h1, hp₁, hp₂]
      exact t
    have hpk : D.pos (π₂, y₂) = D.pos k := hp₂.trans hkpos.symm
    exact ⟨h1, (π₁, y₁), hr₁, (D.lifts_fwd (X.tri_edge12 t) q (π₁, y₁) s').mpr
      ⟨hp₁, (π₂, y₂), hr₂, D.lifts_of_start q (D.rel_of_fork hr₀₂ hk hpk) hpk hq⟩⟩

/-- Lifts are invariant under an elementary homotopy move. -/
theorem lifts_iff_of_move {a d : V} {p q : X.EdgePath a d} (h : EdgePath.Move p q)
    (s s' : D.State) : D.Lifts p s s' ↔ D.Lifts q s s' := by
  cases h with
  | backtrackFwd r e w =>
    rw [D.lifts_append r, D.lifts_append r]
    exact exists_congr fun m => and_congr_right fun _ => D.lifts_backtrack_fwd e w m s'
  | backtrackBwd r e w =>
    rw [D.lifts_append r, D.lifts_append r]
    exact exists_congr fun m => and_congr_right fun _ => D.lifts_backtrack_bwd e w m s'
  | triangle r t w =>
    rw [D.lifts_append r, D.lifts_append r]
    exact exists_congr fun m => and_congr_right fun _ => D.lifts_triangle t w m s'

/-- Lifts are invariant under combinatorial homotopy. -/
theorem lifts_iff_of_homotopic {a d : V} {p q : X.EdgePath a d} (h : EdgePath.Homotopic p q)
    (s s' : D.State) : D.Lifts p s s' ↔ D.Lifts q s s' := by
  have h' : Relation.EqvGen EdgePath.Move p q := h
  clear h
  induction h' with
  | rel _ _ hm => exact D.lifts_iff_of_move hm s s'
  | refl _ => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

#audit_axioms GroupApproximation.Full.LVBrown.Datum.lifts_iff_of_homotopic

end Datum

end GroupApproximation.Full.LVBrown
