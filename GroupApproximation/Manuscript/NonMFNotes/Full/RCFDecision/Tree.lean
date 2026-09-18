import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Poly

/-!
# Quantifier-free formulas and guarded case trees

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof step "Fixed-dimensional
feasibility is decidable over the real closed field".  Eliminating a quantifier
means computing with polynomials whose coefficients depend on the remaining
variables.  Whenever the computation needs the sign of such a coefficient, it
branches on that sign.  The result is a *guarded case tree*: a list of leaves, each a
conjunction of atoms (the guard) together with a value.

* `Atom`: `(true, p)` is `0 < p` and `(false, p)` is `p = 0`; `QF` is a
  disjunction of conjunctions of atoms, with truth `qfHolds`;
* `qfAnd`, `qfNot`: conjunction and negation of `QF` formulas;
* `qfZ`: evaluation of a `QF` formula at the zero assignment by integer
  arithmetic (`qfZ_iff`);
* `tpure`, `tbind`, `tmap`, `tseq`: the case-tree monad, and `Good ρ t R`: at
  `ρ` some guard holds and every leaf whose guard holds satisfies `R`;
* `toQF`: a Boolean case tree as a formula (`qfHolds_toQF`).
-/

namespace GroupApproximation.Full.NN11b

/-! ## Atoms and formulas -/

/-- An atom: `(true, p)` stands for `0 < p`, `(false, p)` for `p = 0`. -/
abbrev Atom := Bool × List (ℤ × List ℕ)

/-- Truth of an atom at an assignment. -/
def atomHolds (ρ : ℕ → ℝ) : Bool × List (ℤ × List ℕ) → Prop
  | (true, p) => 0 < mvEval ρ p
  | (false, p) => mvEval ρ p = 0

theorem atomHolds_true (ρ : ℕ → ℝ) (p : MvP) :
    atomHolds ρ (true, p) ↔ 0 < mvEval ρ p := Iff.rfl

theorem atomHolds_false (ρ : ℕ → ℝ) (p : MvP) :
    atomHolds ρ (false, p) ↔ mvEval ρ p = 0 := Iff.rfl

/-- Truth of a conjunction of atoms. -/
def guardHolds (ρ : ℕ → ℝ) (g : List Atom) : Prop := ∀ a ∈ g, atomHolds ρ a

theorem guardHolds_nil (ρ : ℕ → ℝ) : guardHolds ρ [] := by
  unfold guardHolds
  intro _ h
  exact absurd h List.not_mem_nil

theorem guardHolds_append (ρ : ℕ → ℝ) (g h : List Atom) :
    guardHolds ρ (g ++ h) ↔ guardHolds ρ g ∧ guardHolds ρ h := by
  unfold guardHolds
  exact List.forall_mem_append

theorem guardHolds_cons (ρ : ℕ → ℝ) (a : Atom) (g : List Atom) :
    guardHolds ρ (a :: g) ↔ atomHolds ρ a ∧ guardHolds ρ g := by
  unfold guardHolds
  exact List.forall_mem_cons

theorem guardHolds_singleton (ρ : ℕ → ℝ) (a : Atom) : guardHolds ρ [a] ↔ atomHolds ρ a := by
  rw [guardHolds_cons]
  exact ⟨fun h => h.1, fun h => ⟨h, guardHolds_nil ρ⟩⟩

/-- Quantifier-free formulas in disjunctive normal form. -/
abbrev QF := List (List Atom)

/-- Truth of a formula in disjunctive normal form. -/
def qfHolds (ρ : ℕ → ℝ) (f : List (List Atom)) : Prop := ∃ c ∈ f, guardHolds ρ c

theorem qfHolds_nil (ρ : ℕ → ℝ) : ¬ qfHolds ρ [] := by
  unfold qfHolds
  rintro ⟨_, hc, _⟩
  exact List.not_mem_nil hc

theorem qfHolds_cons (ρ : ℕ → ℝ) (c : List Atom) (f : QF) :
    qfHolds ρ (c :: f) ↔ guardHolds ρ c ∨ qfHolds ρ f := by
  unfold qfHolds
  constructor
  · rintro ⟨d, hd, hg⟩
    rcases List.mem_cons.1 hd with h | h
    · subst h
      exact Or.inl hg
    · exact Or.inr ⟨d, h, hg⟩
  · rintro (h | ⟨d, hd, hg⟩)
    · exact ⟨c, List.mem_cons_self, h⟩
    · exact ⟨d, List.mem_cons_of_mem c hd, hg⟩

theorem qfHolds_append (ρ : ℕ → ℝ) (f g : QF) :
    qfHolds ρ (f ++ g) ↔ qfHolds ρ f ∨ qfHolds ρ g := by
  unfold qfHolds
  constructor
  · rintro ⟨d, hd, hg⟩
    rcases List.mem_append.1 hd with h | h
    · exact Or.inl ⟨d, h, hg⟩
    · exact Or.inr ⟨d, h, hg⟩
  · rintro (⟨d, hd, hg⟩ | ⟨d, hd, hg⟩)
    · exact ⟨d, List.mem_append.2 (Or.inl hd), hg⟩
    · exact ⟨d, List.mem_append.2 (Or.inr hd), hg⟩

/-- Conjunction of formulas in disjunctive normal form. -/
def qfAnd (f g : List (List Atom)) : List (List Atom) :=
  f.flatMap fun c => g.map fun d => c ++ d

theorem qfHolds_and (ρ : ℕ → ℝ) (f g : QF) :
    qfHolds ρ (qfAnd f g) ↔ qfHolds ρ f ∧ qfHolds ρ g := by
  unfold qfHolds qfAnd
  constructor
  · rintro ⟨e, he, hg⟩
    obtain ⟨c, hc, he'⟩ := List.mem_flatMap.1 he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 he'
    have hcd := (guardHolds_append ρ c d).1 hg
    exact ⟨⟨c, hc, hcd.1⟩, ⟨d, hd, hcd.2⟩⟩
  · rintro ⟨⟨c, hc, hgc⟩, ⟨d, hd, hgd⟩⟩
    exact ⟨c ++ d, List.mem_flatMap.2 ⟨c, hc, List.mem_map.2 ⟨d, hd, rfl⟩⟩,
      (guardHolds_append ρ c d).2 ⟨hgc, hgd⟩⟩

/-- The negation of an atom, as a formula. -/
def negAtom : Bool × List (ℤ × List ℕ) → List (List Atom)
  | (true, p) => [[(false, p)], [(true, mvNeg p)]]
  | (false, p) => [[(true, p)], [(true, mvNeg p)]]

theorem qfHolds_negAtom (ρ : ℕ → ℝ) : ∀ a : Atom, qfHolds ρ (negAtom a) ↔ ¬ atomHolds ρ a
  | (true, p) => by
      show qfHolds ρ [[(false, p)], [(true, mvNeg p)]] ↔ ¬ atomHolds ρ (true, p)
      rw [qfHolds_cons, qfHolds_cons, guardHolds_singleton, guardHolds_singleton,
        atomHolds_false, atomHolds_true, atomHolds_true, mvEval_neg]
      have hnil := qfHolds_nil ρ
      constructor
      · rintro (h | h | h)
        · intro h'
          linarith
        · intro h'
          linarith
        · exact absurd h hnil
      · intro h
        rcases lt_trichotomy (mvEval ρ p) 0 with h1 | h1 | h1
        · exact Or.inr (Or.inl (by linarith))
        · exact Or.inl h1
        · exact absurd h1 h
  | (false, p) => by
      show qfHolds ρ [[(true, p)], [(true, mvNeg p)]] ↔ ¬ atomHolds ρ (false, p)
      rw [qfHolds_cons, qfHolds_cons, guardHolds_singleton, guardHolds_singleton,
        atomHolds_true, atomHolds_true, atomHolds_false, mvEval_neg]
      have hnil := qfHolds_nil ρ
      constructor
      · rintro (h | h | h)
        · intro h'
          linarith
        · intro h'
          linarith
        · exact absurd h hnil
      · intro h
        rcases lt_trichotomy (mvEval ρ p) 0 with h1 | h1 | h1
        · exact Or.inr (Or.inl (by linarith))
        · exact absurd h1 h
        · exact Or.inl h1

theorem qfHolds_negClause (ρ : ℕ → ℝ) : ∀ c : List Atom,
    qfHolds ρ (c.flatMap negAtom) ↔ ¬ guardHolds ρ c
  | [] => by
      show qfHolds ρ [] ↔ ¬ guardHolds ρ []
      exact ⟨fun h => absurd h (qfHolds_nil ρ), fun h => absurd (guardHolds_nil ρ) h⟩
  | a :: c => by
      rw [List.flatMap_cons, qfHolds_append, qfHolds_negAtom, qfHolds_negClause ρ c,
        guardHolds_cons, not_and_or]

/-- Negation of a formula in disjunctive normal form. -/
def qfNot : List (List Atom) → List (List Atom)
  | [] => [[]]
  | c :: f => qfAnd (c.flatMap negAtom) (qfNot f)

theorem qfHolds_not (ρ : ℕ → ℝ) : ∀ f : QF, qfHolds ρ (qfNot f) ↔ ¬ qfHolds ρ f
  | [] => by
      show qfHolds ρ [[]] ↔ ¬ qfHolds ρ []
      rw [qfHolds_cons]
      exact ⟨fun _ => qfHolds_nil ρ, fun _ => Or.inl (guardHolds_nil ρ)⟩
  | c :: f => by
      show qfHolds ρ (qfAnd (c.flatMap negAtom) (qfNot f)) ↔ ¬ qfHolds ρ (c :: f)
      rw [qfHolds_and, qfHolds_negClause, qfHolds_not ρ f, qfHolds_cons, not_or]

/-! ## Evaluation at the zero assignment -/

/-- The value of a monomial at the zero assignment. -/
def monoZ : List ℕ → ℤ
  | [] => 1
  | k :: e => (if k = 0 then 1 else 0) * monoZ e

theorem monoEval_zero : ∀ e : List ℕ, monoEval (fun _ => 0) e = (monoZ e : ℝ)
  | [] => by
      show (1 : ℝ) = ((1 : ℤ) : ℝ)
      rw [Int.cast_one]
  | k :: e => by
      show (0 : ℝ) ^ k * monoEval (fun _ => 0) e
        = (((if k = 0 then 1 else 0) * monoZ e : ℤ) : ℝ)
      rw [monoEval_zero e, Int.cast_mul]
      by_cases hk : k = 0
      · subst hk
        rw [pow_zero, if_pos (rfl : (0 : ℕ) = 0), Int.cast_one]
      · rw [zero_pow hk, if_neg hk, Int.cast_zero]

/-- The value of a polynomial at the zero assignment. -/
def mvZ : List (ℤ × List ℕ) → ℤ
  | [] => 0
  | m :: p => m.1 * monoZ m.2 + mvZ p

theorem mvEval_zero : ∀ p : MvP, mvEval (fun _ => 0) p = (mvZ p : ℝ)
  | [] => by
      show (0 : ℝ) = ((0 : ℤ) : ℝ)
      rw [Int.cast_zero]
  | m :: p => by
      show (m.1 : ℝ) * monoEval (fun _ => 0) m.2 + mvEval (fun _ => 0) p
        = ((m.1 * monoZ m.2 + mvZ p : ℤ) : ℝ)
      rw [monoEval_zero, mvEval_zero p, Int.cast_add, Int.cast_mul]

/-- Truth value of an atom at the zero assignment. -/
def atomZ : Bool × List (ℤ × List ℕ) → Bool
  | (true, p) => decide (0 < mvZ p)
  | (false, p) => decide (mvZ p = 0)

theorem atomZ_iff : ∀ a : Atom, atomZ a = true ↔ atomHolds (fun _ => 0) a
  | (true, p) => by
      show decide (0 < mvZ p) = true ↔ 0 < mvEval (fun _ => 0) p
      rw [decide_eq_true_iff, mvEval_zero, Int.cast_pos]
  | (false, p) => by
      show decide (mvZ p = 0) = true ↔ mvEval (fun _ => 0) p = 0
      rw [decide_eq_true_iff, mvEval_zero, Int.cast_eq_zero]

/-- Truth value of a formula at the zero assignment. -/
def qfZ (f : List (List Atom)) : Bool := f.any fun c => c.all atomZ

theorem qfZ_iff (f : QF) : qfZ f = true ↔ qfHolds (fun _ => 0) f := by
  unfold qfZ qfHolds guardHolds
  rw [List.any_eq_true]
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, fun a ha => (atomZ_iff a).1 (List.all_eq_true.1 h a ha)⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, List.all_eq_true.2 fun a ha => (atomZ_iff a).2 (h a ha)⟩

/-! ## Guarded case trees -/

/-- A case tree: leaves carry a guard and a value. -/
abbrev Tree (α : Type) := List (List Atom × α)

/-- The one-leaf tree. -/
def tpure {α : Type} (a : α) : List (List Atom × α) := [([], a)]

/-- Strengthening all guards of a tree. -/
def guardT {α : Type} (g : List Atom) (t : List (List Atom × α)) : List (List Atom × α) :=
  t.map fun l => (g ++ l.1, l.2)

/-- Substituting a tree into each leaf. -/
def tbind {α β : Type} (t : List (List Atom × α)) (f : α → List (List Atom × β)) :
    List (List Atom × β) :=
  t.flatMap fun l => guardT l.1 (f l.2)

/-- Applying a function to the leaf values. -/
def tmap {α β : Type} (f : α → β) (t : List (List Atom × α)) : List (List Atom × β) :=
  t.map fun l => (l.1, f l.2)

/-- `t` is a correct case tree at `ρ` for the leaf property `R`: some guard
holds at `ρ`, and every leaf whose guard holds satisfies `R`. -/
structure Good {α : Type} (ρ : ℕ → ℝ) (t : List (List Atom × α)) (R : α → Prop) : Prop where
  sound : ∀ l ∈ t, guardHolds ρ l.1 → R l.2
  covers : ∃ l ∈ t, guardHolds ρ l.1

theorem good_pure {α : Type} (ρ : ℕ → ℝ) {R : α → Prop} {a : α} (h : R a) :
    Good ρ (tpure a) R := by
  refine ⟨fun l hl _ => ?_, ⟨([], a), List.mem_singleton_self _, guardHolds_nil ρ⟩⟩
  have hl' : l = ([], a) := List.mem_singleton.1 hl
  subst hl'
  exact h

theorem good_mono {α : Type} {ρ : ℕ → ℝ} {t : List (List Atom × α)} {R R' : α → Prop}
    (h : Good ρ t R) (hR : ∀ a, R a → R' a) : Good ρ t R' :=
  ⟨fun l hl hg => hR _ (h.sound l hl hg), h.covers⟩

theorem good_bind {α β : Type} {ρ : ℕ → ℝ} {t : List (List Atom × α)}
    {f : α → List (List Atom × β)} {R : β → Prop}
    (h : Good ρ t fun a => Good ρ (f a) R) : Good ρ (tbind t f) R := by
  constructor
  · intro l hl hg
    unfold tbind at hl
    obtain ⟨m, hm, hl'⟩ := List.mem_flatMap.1 hl
    unfold guardT at hl'
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hl'
    have hg' := (guardHolds_append ρ m.1 k.1).1 hg
    exact (h.sound m hm hg'.1).sound k hk hg'.2
  · obtain ⟨m, hm, hgm⟩ := h.covers
    obtain ⟨k, hk, hgk⟩ := (h.sound m hm hgm).covers
    refine ⟨(m.1 ++ k.1, k.2), ?_, (guardHolds_append ρ m.1 k.1).2 ⟨hgm, hgk⟩⟩
    unfold tbind
    refine List.mem_flatMap.2 ⟨m, hm, ?_⟩
    unfold guardT
    exact List.mem_map.2 ⟨k, hk, rfl⟩

theorem good_tmap {α β : Type} {ρ : ℕ → ℝ} {t : List (List Atom × α)} {f : α → β}
    {R : β → Prop} (h : Good ρ t fun a => R (f a)) : Good ρ (tmap f t) R := by
  constructor
  · intro l hl hg
    unfold tmap at hl
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hl
    exact h.sound k hk hg
  · obtain ⟨k, hk, hgk⟩ := h.covers
    refine ⟨(k.1, f k.2), ?_, hgk⟩
    unfold tmap
    exact List.mem_map.2 ⟨k, hk, rfl⟩

/-- Pointwise relation between two lists of equal length. -/
def AllRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: l, b :: vs => R a b ∧ AllRel R l vs
  | [], _ :: _ => False
  | _ :: _, [] => False

/-- Sequencing a list of trees. -/
def tseq {α : Type} : List (List (List Atom × α)) → List (List Atom × List α)
  | [] => tpure []
  | t :: ts => tbind t fun a => tmap (List.cons a) (tseq ts)

theorem good_tseq {α β : Type} (ρ : ℕ → ℝ) (R : β → α → Prop)
    (f : β → List (List Atom × α)) :
    ∀ l : List β, (∀ x ∈ l, Good ρ (f x) (R x)) → Good ρ (tseq (l.map f)) (AllRel R l)
  | [], _ => by
      show Good ρ (tpure []) (AllRel R [])
      exact good_pure ρ trivial
  | x :: l, h => by
      show Good ρ (tbind (f x) fun a => tmap (List.cons a) (tseq (l.map f))) (AllRel R (x :: l))
      apply good_bind
      refine good_mono (h x List.mem_cons_self) fun a ha => ?_
      apply good_tmap
      refine good_mono (good_tseq ρ R f l fun y hy => h y (List.mem_cons_of_mem x hy))
        fun vs hvs => ?_
      exact ⟨ha, hvs⟩

/-- A Boolean case tree as a formula: the disjunction of the guards of its
`true` leaves. -/
def toQF (t : List (List Atom × Bool)) : List (List Atom) :=
  (t.filter fun l => l.2).map fun l => l.1

theorem qfHolds_toQF {ρ : ℕ → ℝ} {t : List (List Atom × Bool)} {P : Prop}
    (h : Good ρ t fun b => (b = true ↔ P)) : qfHolds ρ (toQF t) ↔ P := by
  unfold qfHolds toQF
  constructor
  · rintro ⟨c, hc, hg⟩
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hc
    obtain ⟨hlt, hl2⟩ := List.mem_filter.1 hl
    exact (h.sound l hlt hg).1 hl2
  · intro hP
    obtain ⟨l, hl, hg⟩ := h.covers
    exact ⟨l.1, List.mem_map.2 ⟨l, List.mem_filter.2 ⟨hl, (h.sound l hl hg).2 hP⟩, rfl⟩, hg⟩

end GroupApproximation.Full.NN11b
