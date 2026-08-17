import GroupApproximation.Computability.RewriteSimulationOn

/-!
# A machine with an unbounded tape, simulated by a finite rewriting system

This is Post's construction, in the form `SimulationOn` consumes.

A deterministic machine is encoded so that a configuration becomes a word
carrying exactly one state letter, and each transition becomes a rewriting rule
firing at that letter.  The four `SimulationOn` conditions are discharged here,
so `SimulationOn.derives_iff` applies: two configurations are equal in the
presented monoid exactly when the machine drives them to a common one, and by
`SimulationOn.eq_of_derives_of_halts` distinct halts stay distinct.

## The one lemma that does the work

Everything reduces to `eq_of_stateFree_prefix`: if two decompositions of a word
put a state letter at the head of their tails and have state-free prefixes, the
decompositions agree.  Every rule's left-hand side carries exactly one state
letter and a configuration word carries exactly one, so this pins *where* a rule
can fire.  The case analysis over "which occurrence matched" collapses before it
starts, which is the step that makes a machine simulation feasible at all.

The same fact gives backward closure: each rule has one state letter on both
sides, so a word rewriting *into* a configuration had one too.

## Why the tape has to be unbounded

An earlier version of this file had the machine *halt* when a move would run off
its tape.  That kept the rule set to three shapes, and every proof below went
through --- but the resulting theorem was worthless.  A machine on a bounded
tape has finitely many configurations reachable from any start, so its halting
problem is decidable, and a word problem that decides a decidable problem
decides nothing.  The point of simulating a machine by a monoid is to inherit
*undecidability*, so the tape must actually be unbounded.

The fix is end markers.  A configuration word is bracketed by `endL` and `endR`;
a move that would leave the written portion instead writes a fresh blank inside
the marker, so the tape grows on demand and the machine never runs off it.  This
costs two extra rule shapes, one per direction, and in the proofs one extra
observation: a word of tape letters neither begins nor ends with a marker, so a
marker occurring in a rule can only match the real one.  That is
`map_tape_eq_snoc`, `pre_eq_snoc` and `post_eq_cons` below, and it is why no
second counting invariant --- for the markers --- is needed.

The machine now halts exactly when its transition function says so, and halting
configurations are still automatically normal forms.
-/

namespace GroupApproximation
namespace StringRewriting
namespace PostMachine

/-- Letters of the encoding alphabet: tape symbols, state symbols, and the two
end markers that let the tape grow. -/
inductive Letter (Γ Λ : Type) where
  | tape : Γ → Letter Γ Λ
  | state : Λ → Letter Γ Λ
  | endL : Letter Γ Λ
  | endR : Letter Γ Λ
  deriving DecidableEq

/-- What a transition does. -/
inductive Action (Γ : Type) where
  | write : Γ → Action Γ
  | moveLeft : Action Γ
  | moveRight : Action Γ
  deriving DecidableEq

/-- A deterministic machine. -/
abbrev Machine (Γ Λ : Type) := Λ → Γ → Option (Λ × Action Γ)

/-- A configuration: state, the written tape left of the head (nearest first),
the scanned symbol, and the written tape right of the head.  Tape beyond those
lists is blank, and is materialised on demand. -/
structure Cfg (Γ Λ : Type) where
  q : Λ
  left : List Γ
  head : Γ
  right : List Γ
  deriving DecidableEq

variable {Γ Λ : Type}

/-- Whether a letter is a state letter. -/
def isState : Letter Γ Λ → Bool
  | .tape _ => false
  | .state _ => true
  | .endL => false
  | .endR => false

@[simp] theorem isState_tape (a : Γ) :
    isState (Letter.tape a : Letter Γ Λ) = false := rfl

@[simp] theorem isState_state (q : Λ) :
    isState (Letter.state q : Letter Γ Λ) = true := rfl

@[simp] theorem isState_endL : isState (Letter.endL : Letter Γ Λ) = false := rfl

@[simp] theorem isState_endR : isState (Letter.endR : Letter Γ Λ) = false := rfl

/-- A word is state-free when none of its letters is a state letter. -/
def StateFree (w : List (Letter Γ Λ)) : Prop := ∀ x ∈ w, isState x = false

theorem stateFree_map_tape (l : List Γ) :
    StateFree (l.map (Letter.tape : Γ → Letter Γ Λ)) := by
  intro x hx
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
  rfl

theorem stateFree_cons {z : Letter Γ Λ} {w : List (Letter Γ Λ)}
    (hz : isState z = false) (hw : StateFree w) : StateFree (z :: w) := by
  intro x hx
  rcases List.mem_cons.mp hx with h | h
  · rw [h]; exact hz
  · exact hw x h

theorem stateFree_snoc {w : List (Letter Γ Λ)} (hw : StateFree w)
    {z : Letter Γ Λ} (hz : isState z = false) : StateFree (w ++ [z]) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hw x h
  · simp only [List.mem_singleton] at h
    rw [h]; exact hz

theorem countP_map_tape (l : List Γ) :
    (l.map (Letter.tape : Γ → Letter Γ Λ)).countP isState = 0 := by
  rw [List.countP_eq_zero]
  intro x hx
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
  simp

/-- `simp` normalises `countP` through a `map` into a composition, so the
zero-count fact has to be available in that form too. -/
@[simp] theorem countP_comp_tape (l : List Γ) :
    l.countP (isState ∘ (Letter.tape : Γ → Letter Γ Λ)) = 0 := by
  rw [List.countP_eq_zero]
  intro x _
  simp

theorem stateFree_of_countP_zero {w : List (Letter Γ Λ)}
    (h : w.countP isState = 0) : StateFree w := by
  intro x hx
  have := List.countP_eq_zero.mp h x hx
  simpa using this

/-- **The pinning lemma.**  A word can be cut just before a state letter with a
state-free prefix in at most one way. -/
theorem eq_of_stateFree_prefix :
    ∀ {u p : List (Letter Γ Λ)} {s s' : Λ} {t t' : List (Letter Γ Λ)},
      StateFree u → StateFree p →
      u ++ (Letter.state s :: t) = p ++ (Letter.state s' :: t') →
      u = p ∧ s = s' ∧ t = t' := by
  intro u
  induction u with
  | nil =>
    intro p s s' t t' _ hp h
    cases p with
    | nil =>
      simp only [List.nil_append] at h
      obtain ⟨h1, h2⟩ := List.cons.inj h
      exact ⟨rfl, by simpa using h1, h2⟩
    | cons y r =>
      simp only [List.nil_append, List.cons_append] at h
      obtain ⟨h1, _⟩ := List.cons.inj h
      have : isState y = true := by rw [← h1]; simp
      have hy := hp y (by simp)
      rw [hy] at this
      exact absurd this (by simp)
  | cons x u ih =>
    intro p s s' t t' hu hp h
    cases p with
    | nil =>
      simp only [List.nil_append, List.cons_append] at h
      obtain ⟨h1, _⟩ := List.cons.inj h
      have : isState x = true := by rw [h1]; simp
      have hx := hu x (by simp)
      rw [hx] at this
      exact absurd this (by simp)
    | cons y r =>
      simp only [List.cons_append] at h
      obtain ⟨hxy, htail⟩ := List.cons.inj h
      have hu' : StateFree u := fun z hz => hu z (by simp [hz])
      have hp' : StateFree r := fun z hz => hp z (by simp [hz])
      obtain ⟨h1, h2, h3⟩ := ih hu' hp' htail
      exact ⟨by rw [hxy, h1], h2, h3⟩

/-! ## The encoding

None of this mentions the machine: a configuration word is built from the
configuration alone, and the lemmas that read one back are pure list facts. -/

/-- The part of a configuration word before the state letter: the left marker,
then the tape written to the left of the head. -/
def pre (c : Cfg Γ Λ) : List (Letter Γ Λ) :=
  Letter.endL :: c.left.reverse.map Letter.tape

/-- The part after the state letter: the scanned symbol, the tape written to its
right, then the right marker. -/
def post (c : Cfg Γ Λ) : List (Letter Γ Λ) :=
  Letter.tape c.head :: (c.right.map Letter.tape ++ [Letter.endR])

/-- A configuration as a word. -/
def encode (c : Cfg Γ Λ) : List (Letter Γ Λ) :=
  pre c ++ (Letter.state c.q :: post c)

@[simp] theorem encode_eq (c : Cfg Γ Λ) :
    encode c = pre c ++ (Letter.state c.q :: post c) := rfl

theorem stateFree_pre (c : Cfg Γ Λ) : StateFree (pre c) :=
  stateFree_cons rfl (stateFree_map_tape _)

theorem countP_encode (c : Cfg Γ Λ) :
    (encode c).countP (isState : Letter Γ Λ → Bool) = 1 := by
  simp [encode, pre, post]

/-! ## Reading words of tape letters

These keep the markers honest: a word of tape letters neither begins nor ends
with a marker, so a marker occurring in a rule can only match the real one. -/

/-- The tape letters of a word determine the tape symbols. -/
theorem map_tape_injective :
    Function.Injective (List.map (Letter.tape : Γ → Letter Γ Λ)) := by
  intro l m h
  induction l generalizing m with
  | nil => cases m with
    | nil => rfl
    | cons b m => simp at h
  | cons a l ih =>
    cases m with
    | nil => simp at h
    | cons b m =>
      simp only [List.map_cons] at h
      obtain ⟨h1, h2⟩ := List.cons.inj h
      have : a = b := by injection h1
      rw [this, ih h2]

/-- A word of tape letters ends in a tape letter, and the rest is again a word
of tape letters. -/
theorem map_tape_eq_snoc {l : List Γ} {u : List (Letter Γ Λ)} {z : Letter Γ Λ}
    (h : u ++ [z] = l.map Letter.tape) :
    ∃ m y, l = m ++ [y] ∧ z = Letter.tape y ∧ u = m.map Letter.tape := by
  induction l generalizing u with
  | nil => simp at h
  | cons a l ih =>
    cases u with
    | nil =>
      simp only [List.nil_append, List.map_cons] at h
      obtain ⟨h1, h2⟩ := List.cons.inj h
      have hl : l = [] := by simpa using h2.symm
      exact ⟨[], a, by simp [hl], h1, rfl⟩
    | cons w u =>
      simp only [List.cons_append, List.map_cons] at h
      obtain ⟨h1, h2⟩ := List.cons.inj h
      obtain ⟨m, y, hm1, hm2, hm3⟩ := ih h2
      exact ⟨a :: m, y, by simp [hm1], hm2, by simp [h1, hm3]⟩

/-- Reading the left frame off a snoc: either it is the marker alone --- and
then the head is at the left end of the written tape --- or the last letter is a
tape letter. -/
theorem pre_eq_snoc {c : Cfg Γ Λ} {u : List (Letter Γ Λ)} {z : Letter Γ Λ}
    (h : u ++ [z] = pre c) :
    (u = [] ∧ z = Letter.endL ∧ c.left = []) ∨
      (∃ (m : List Γ) (y : Γ), u = Letter.endL :: m.map Letter.tape ∧
        z = Letter.tape y ∧ c.left = y :: m.reverse) := by
  rw [pre] at h
  cases u with
  | nil =>
    simp only [List.nil_append] at h
    obtain ⟨h1, h2⟩ := List.cons.inj h
    refine Or.inl ⟨rfl, h1, ?_⟩
    have hrev : c.left.reverse = [] := by simpa using h2.symm
    simpa using congrArg List.reverse hrev
  | cons w u =>
    simp only [List.cons_append] at h
    obtain ⟨h1, h2⟩ := List.cons.inj h
    obtain ⟨m, y, hm1, hm2, hm3⟩ := map_tape_eq_snoc h2
    refine Or.inr ⟨m, y, by rw [h1, hm3], hm2, ?_⟩
    have := congrArg List.reverse hm1
    simpa using this

/-- Reading the right frame off a cons: either the tape right of the head is
empty and the next letter is the marker, or it is a tape letter. -/
theorem post_eq_cons {R : List Γ} {z : Letter Γ Λ} {v : List (Letter Γ Λ)}
    (h : z :: v = R.map Letter.tape ++ [Letter.endR]) :
    (R = [] ∧ z = Letter.endR ∧ v = []) ∨
      (∃ x r, R = x :: r ∧ z = Letter.tape x ∧
        v = r.map Letter.tape ++ [Letter.endR]) := by
  cases R with
  | nil =>
    simp only [List.map_nil, List.nil_append] at h
    obtain ⟨h1, h2⟩ := List.cons.inj h
    exact Or.inl ⟨rfl, h1, h2⟩
  | cons x r =>
    simp only [List.map_cons, List.cons_append] at h
    obtain ⟨h1, h2⟩ := List.cons.inj h
    exact Or.inr ⟨x, r, rfl, h1, h2⟩

theorem encode_injective : Function.Injective (encode : Cfg Γ Λ → _) := by
  intro c d h
  obtain ⟨h1, h2, h3⟩ :=
    eq_of_stateFree_prefix (stateFree_pre c) (stateFree_pre d) h
  rw [pre, pre] at h1
  obtain ⟨_, h1'⟩ := List.cons.inj h1
  rw [post, post] at h3
  obtain ⟨hh, hr⟩ := List.cons.inj h3
  have hhead : c.head = d.head := by injection hh
  have hleft : c.left = d.left := by
    have := map_tape_injective h1'
    simpa using congrArg List.reverse this
  have hright : c.right = d.right :=
    map_tape_injective (List.append_cancel_right hr)
  cases c; cases d
  simp_all

/-- Around a one-state-letter block inside a configuration word, the context is
state-free. -/
theorem stateFree_context {u m v : List (Letter Γ Λ)} {c : Cfg Γ Λ}
    (h : u ++ m ++ v = encode c) (hm : m.countP isState = 1) :
    StateFree u ∧ StateFree v := by
  have htot : (u ++ m ++ v).countP (isState : Letter Γ Λ → Bool) = 1 := by
    rw [h]; exact countP_encode c
  rw [List.countP_append, List.countP_append, hm] at htot
  constructor
  · exact stateFree_of_countP_zero (by omega)
  · exact stateFree_of_countP_zero (by omega)

/-! ## The machine -/

variable (M : Machine Γ Λ) [Inhabited Γ]

/-- One machine step.  A move past the written portion of the tape materialises
a blank there, so the tape is unbounded and the machine never runs off it; the
machine halts exactly when its transition function says so. -/
def step : Cfg Γ Λ → Option (Cfg Γ Λ) := fun c =>
  match M c.q c.head with
  | none => none
  | some (q', .write b) => some { q := q', left := c.left, head := b, right := c.right }
  | some (q', .moveRight) =>
      match c.right with
      | [] => some { q := q', left := c.head :: c.left, head := default, right := [] }
      | x :: r => some { q := q', left := c.head :: c.left, head := x, right := r }
  | some (q', .moveLeft) =>
      match c.left with
      | [] => some { q := q', left := [], head := default, right := c.head :: c.right }
      | y :: l => some { q := q', left := l, head := y, right := c.head :: c.right }

variable {M}

/-- With an unbounded tape the machine stops for exactly one reason: the
transition function said so. -/
@[simp] theorem step_eq_none_iff (c : Cfg Γ Λ) :
    step M c = none ↔ M c.q c.head = none := by
  unfold step
  cases M c.q c.head with
  | none => simp
  | some p =>
    obtain ⟨q', act⟩ := p
    cases act <;> cases c.left <;> cases c.right <;> simp

/-! ## The rules

Five shapes: one for writing, and for each direction one ordinary move and one
move that materialises a blank at the marker.  Every left-hand side carries
exactly one state letter, and so does every right-hand side; that single fact is
what makes both closure conditions work. -/

variable (M)

/-- The rules of the machine, as a predicate on pairs of words. -/
def IsMachineRule (l r : List (Letter Γ Λ)) : Prop :=
  (∃ q a q' b, M q a = some (q', .write b) ∧
      l = [Letter.state q, Letter.tape a] ∧
      r = [Letter.state q', Letter.tape b]) ∨
  (∃ q a x q', M q a = some (q', .moveRight) ∧
      l = [Letter.state q, Letter.tape a, Letter.tape x] ∧
      r = [Letter.tape a, Letter.state q', Letter.tape x]) ∨
  (∃ q a q', M q a = some (q', .moveRight) ∧
      l = [Letter.state q, Letter.tape a, Letter.endR] ∧
      r = [Letter.tape a, Letter.state q', Letter.tape default, Letter.endR]) ∨
  (∃ q a y q', M q a = some (q', .moveLeft) ∧
      l = [Letter.tape y, Letter.state q, Letter.tape a] ∧
      r = [Letter.state q', Letter.tape y, Letter.tape a]) ∨
  (∃ q a q', M q a = some (q', .moveLeft) ∧
      l = [Letter.endL, Letter.state q, Letter.tape a] ∧
      r = [Letter.endL, Letter.state q', Letter.tape default, Letter.tape a])

/-- A rewriting system presenting exactly the machine's rules. -/
structure Presents (R : RewriteSystem (Letter Γ Λ)) : Prop where
  mem_iff : ∀ l r, (l, r) ∈ R.rules ↔ IsMachineRule M l r

variable {M}

theorem countP_lhs {l r : List (Letter Γ Λ)} (h : IsMachineRule M l r) :
    l.countP isState = 1 := by
  rcases h with ⟨q, a, q', b, _, rfl, _⟩ | ⟨q, a, x, q', _, rfl, _⟩ |
    ⟨q, a, q', _, rfl, _⟩ | ⟨q, a, y, q', _, rfl, _⟩ | ⟨q, a, q', _, rfl, _⟩ <;> simp

theorem countP_rhs {l r : List (Letter Γ Λ)} (h : IsMachineRule M l r) :
    r.countP isState = 1 := by
  rcases h with ⟨q, a, q', b, _, _, rfl⟩ | ⟨q, a, x, q', _, _, rfl⟩ |
    ⟨q, a, q', _, _, rfl⟩ | ⟨q, a, y, q', _, _, rfl⟩ | ⟨q, a, q', _, _, rfl⟩ <;> simp

/-! ## Soundness: a machine step is a rewriting step -/

theorem step_sound_of_subset {R : RewriteSystem (Letter Γ Λ)}
    (hsub : ∀ l r, IsMachineRule M l r → (l, r) ∈ R.rules)
    (c d : Cfg Γ Λ) (h : step M c = some d) : Step R (encode c) (encode d) := by
  unfold step at h
  cases hM : M c.q c.head with
  | none => rw [hM] at h; exact absurd h (by simp)
  | some p =>
    obtain ⟨q', act⟩ := p
    rw [hM] at h
    cases act with
    | write b =>
      have hd : d = ⟨q', c.left, b, c.right⟩ := (Option.some.inj h).symm
      have hmem := hsub _ _
        (Or.inl ⟨c.q, c.head, q', b, hM, rfl, rfl⟩)
      have h1 : encode c =
          pre c ++ [Letter.state c.q, Letter.tape c.head] ++
            (c.right.map Letter.tape ++ [Letter.endR]) := by
        simp [encode, post, List.append_assoc]
      have h2 : encode d =
          pre c ++ [Letter.state q', Letter.tape b] ++
            (c.right.map Letter.tape ++ [Letter.endR]) := by
        rw [hd]; simp [encode, pre, post, List.append_assoc]
      rw [h1, h2]
      exact Step.intro _ _ _ _ hmem
    | moveRight =>
      cases hcr : c.right with
      | nil =>
        rw [hcr] at h
        have hd : d = ⟨q', c.head :: c.left, default, []⟩ :=
          (Option.some.inj h).symm
        have hmem := hsub _ _
          (Or.inr (Or.inr (Or.inl ⟨c.q, c.head, q', hM, rfl, rfl⟩)))
        have h1 : encode c =
            pre c ++ [Letter.state c.q, Letter.tape c.head, Letter.endR] ++ [] := by
          simp [encode, post, hcr]
        have h2 : encode d =
            pre c ++ [Letter.tape c.head, Letter.state q',
              Letter.tape default, Letter.endR] ++ [] := by
          rw [hd]; simp [encode, pre, post, List.append_assoc]
        rw [h1, h2]
        exact Step.intro _ _ _ _ hmem
      | cons x r =>
        rw [hcr] at h
        have hd : d = ⟨q', c.head :: c.left, x, r⟩ := (Option.some.inj h).symm
        have hmem := hsub _ _
          (Or.inr (Or.inl ⟨c.q, c.head, x, q', hM, rfl, rfl⟩))
        have h1 : encode c =
            pre c ++ [Letter.state c.q, Letter.tape c.head, Letter.tape x] ++
              (r.map Letter.tape ++ [Letter.endR]) := by
          simp [encode, post, hcr, List.append_assoc]
        have h2 : encode d =
            pre c ++ [Letter.tape c.head, Letter.state q', Letter.tape x] ++
              (r.map Letter.tape ++ [Letter.endR]) := by
          rw [hd]; simp [encode, pre, post, List.append_assoc]
        rw [h1, h2]
        exact Step.intro _ _ _ _ hmem
    | moveLeft =>
      cases hcl : c.left with
      | nil =>
        rw [hcl] at h
        have hd : d = ⟨q', [], default, c.head :: c.right⟩ :=
          (Option.some.inj h).symm
        have hmem := hsub _ _
          (Or.inr (Or.inr (Or.inr (Or.inr ⟨c.q, c.head, q', hM, rfl, rfl⟩))))
        have h1 : encode c =
            [] ++ [Letter.endL, Letter.state c.q, Letter.tape c.head] ++
              (c.right.map Letter.tape ++ [Letter.endR]) := by
          simp [encode, pre, post, hcl]
        have h2 : encode d =
            [] ++ [Letter.endL, Letter.state q', Letter.tape default,
              Letter.tape c.head] ++ (c.right.map Letter.tape ++ [Letter.endR]) := by
          rw [hd]; simp [encode, pre, post]
        rw [h1, h2]
        exact Step.intro _ _ _ _ hmem
      | cons y l =>
        rw [hcl] at h
        have hd : d = ⟨q', l, y, c.head :: c.right⟩ :=
          (Option.some.inj h).symm
        have hmem := hsub _ _
          (Or.inr (Or.inr (Or.inr (Or.inl ⟨c.q, c.head, y, q', hM, rfl, rfl⟩))))
        have h1 : encode c =
            (Letter.endL :: l.reverse.map Letter.tape) ++
              [Letter.tape y, Letter.state c.q, Letter.tape c.head] ++
              (c.right.map Letter.tape ++ [Letter.endR]) := by
          simp [encode, pre, post, hcl, List.append_assoc]
        have h2 : encode d =
            (Letter.endL :: l.reverse.map Letter.tape) ++
              [Letter.state q', Letter.tape y, Letter.tape c.head] ++
              (c.right.map Letter.tape ++ [Letter.endR]) := by
          rw [hd]; simp [encode, pre, post, List.append_assoc]
        rw [h1, h2]
        exact Step.intro _ _ _ _ hmem

/-- A machine step is a rewriting step.  Only one direction of `Presents` is
used, which is what lets a system with extra rules reuse this. -/
theorem step_sound {R : RewriteSystem (Letter Γ Λ)} (hR : Presents M R)
    (c d : Cfg Γ Λ) (h : step M c = some d) : Step R (encode c) (encode d) :=
  step_sound_of_subset (fun l r hlr => (hR.mem_iff l r).mpr hlr) c d h

/-! ## Completeness: a rewriting step out of a configuration is a machine step -/

theorem step_complete_of_rule {u v l r : List (Letter Γ Λ)} {c : Cfg Γ Λ}
    (hrule : IsMachineRule M l r) (hgen : encode c = u ++ l ++ v) :
    ∃ d, step M c = some d ∧ u ++ r ++ v = encode d := by
  obtain ⟨hu, hv⟩ := stateFree_context (c := c) hgen.symm (countP_lhs hrule)
  rcases hrule with ⟨q, a, q', b, hM, rfl, rfl⟩ | ⟨q, a, x, q', hM, rfl, rfl⟩ |
    ⟨q, a, q', hM, rfl, rfl⟩ | ⟨q, a, y, q', hM, rfl, rfl⟩ |
    ⟨q, a, q', hM, rfl, rfl⟩
  · -- write
    have hsplit : u ++ (Letter.state q :: (Letter.tape a :: v)) = encode c := by
      simpa using hgen.symm
    obtain ⟨h1, h2, h3⟩ :=
      eq_of_stateFree_prefix hu (stateFree_pre c) (hsplit.trans (encode_eq c))
    rw [post] at h3
    obtain ⟨h4, h5⟩ := List.cons.inj h3
    have ha : a = c.head := by injection h4
    subst h2
    refine ⟨⟨q', c.left, b, c.right⟩, ?_, ?_⟩
    · unfold step; rw [← ha, hM]
    · rw [h1, h5]; simp [encode, pre, post, List.append_assoc]
  · -- ordinary move right
    have hsplit :
        u ++ (Letter.state q :: (Letter.tape a :: Letter.tape x :: v)) = encode c := by
      simpa using hgen.symm
    obtain ⟨h1, h2, h3⟩ :=
      eq_of_stateFree_prefix hu (stateFree_pre c) (hsplit.trans (encode_eq c))
    rw [post] at h3
    obtain ⟨h4, h5⟩ := List.cons.inj h3
    have ha : a = c.head := by injection h4
    subst h2
    rcases post_eq_cons h5 with ⟨_, hz, _⟩ | ⟨x', r', hcr, hz, hv'⟩
    · exact absurd hz (by simp)
    · have hx : x = x' := by injection hz
      refine ⟨⟨q', c.head :: c.left, x', r'⟩, ?_, ?_⟩
      · unfold step; rw [← ha, hM, hcr]
      · rw [h1, hv', hx, ha]
        simp [encode, pre, post, List.append_assoc]
  · -- move right at the marker
    have hsplit :
        u ++ (Letter.state q :: (Letter.tape a :: Letter.endR :: v)) = encode c := by
      simpa using hgen.symm
    obtain ⟨h1, h2, h3⟩ :=
      eq_of_stateFree_prefix hu (stateFree_pre c) (hsplit.trans (encode_eq c))
    rw [post] at h3
    obtain ⟨h4, h5⟩ := List.cons.inj h3
    have ha : a = c.head := by injection h4
    subst h2
    rcases post_eq_cons h5 with ⟨hcr, _, hv'⟩ | ⟨x', r', _, hz, _⟩
    · refine ⟨⟨q', c.head :: c.left, default, []⟩, ?_, ?_⟩
      · unfold step; rw [← ha, hM, hcr]
      · rw [h1, hv', ha]
        simp [encode, pre, post, List.append_assoc]
    · exact absurd hz.symm (by simp)
  · -- ordinary move left
    have hsplit :
        (u ++ [Letter.tape y]) ++
          (Letter.state q :: (Letter.tape a :: v)) = encode c := by
      simpa [List.append_assoc] using hgen.symm
    obtain ⟨h1, h2, h3⟩ :=
      eq_of_stateFree_prefix (stateFree_snoc hu rfl) (stateFree_pre c)
        (hsplit.trans (encode_eq c))
    rw [post] at h3
    obtain ⟨h4, h5⟩ := List.cons.inj h3
    have ha : a = c.head := by injection h4
    subst h2
    rcases pre_eq_snoc h1 with ⟨_, hz, _⟩ | ⟨m, y', hu', hz, hcl⟩
    · exact absurd hz (by simp)
    · have hy : y = y' := by injection hz
      refine ⟨⟨q', m.reverse, y', c.head :: c.right⟩, ?_, ?_⟩
      · unfold step; rw [← ha, hM, hcl]
      · rw [hu', h5, hy, ha]
        simp [encode, pre, post, List.append_assoc]
  · -- move left at the marker
    have hsplit :
        (u ++ [Letter.endL]) ++
          (Letter.state q :: (Letter.tape a :: v)) = encode c := by
      simpa [List.append_assoc] using hgen.symm
    obtain ⟨h1, h2, h3⟩ :=
      eq_of_stateFree_prefix (stateFree_snoc hu rfl) (stateFree_pre c)
        (hsplit.trans (encode_eq c))
    rw [post] at h3
    obtain ⟨h4, h5⟩ := List.cons.inj h3
    have ha : a = c.head := by injection h4
    subst h2
    rcases pre_eq_snoc h1 with ⟨hu', _, hcl⟩ | ⟨m, y', _, hz, _⟩
    · refine ⟨⟨q', [], default, c.head :: c.right⟩, ?_, ?_⟩
      · unfold step; rw [← ha, hM, hcl]
      · rw [hu', h5, ha]
        simp [encode, pre, post]
    · exact absurd hz (by simp)

/-- A rewriting step out of a configuration is a machine step. -/
theorem step_complete {R : RewriteSystem (Letter Γ Λ)} (hR : Presents M R)
    (c : Cfg Γ Λ) (w : List (Letter Γ Λ)) (hstep : Step R (encode c) w) :
    ∃ d, step M c = some d ∧ w = encode d := by
  generalize hgen : encode c = z at hstep
  cases hstep with
  | intro u v l r hmem => exact step_complete_of_rule ((hR.mem_iff l r).mp hmem) hgen

/-! ## Backward closure: a rewriting step into a configuration starts at one -/

theorem step_closed_inv_of_rule {u v l r : List (Letter Γ Λ)} {c : Cfg Γ Λ}
    (hrule : IsMachineRule M l r) (hgen : encode c = u ++ r ++ v) :
    ∃ d, u ++ l ++ v = encode d := by
  obtain ⟨hu, hv⟩ := stateFree_context (c := c) hgen.symm (countP_rhs hrule)
  rcases hrule with ⟨q, a, q', b, _, rfl, rfl⟩ | ⟨q, a, x, q', _, rfl, rfl⟩ |
    ⟨q, a, q', _, rfl, rfl⟩ | ⟨q, a, y, q', _, rfl, rfl⟩ |
    ⟨q, a, q', _, rfl, rfl⟩
  · -- write
    have hsplit : u ++ (Letter.state q' :: (Letter.tape b :: v)) = encode c := by
      simpa using hgen.symm
    obtain ⟨h1, _, h3⟩ :=
      eq_of_stateFree_prefix hu (stateFree_pre c) (hsplit.trans (encode_eq c))
    rw [post] at h3
    obtain ⟨_, h5⟩ := List.cons.inj h3
    exact ⟨⟨q, c.left, a, c.right⟩, by
      rw [h1, h5]; simp [encode, pre, post, List.append_assoc]⟩
  · -- ordinary move right
    have hsplit :
        (u ++ [Letter.tape a]) ++
          (Letter.state q' :: (Letter.tape x :: v)) = encode c := by
      simpa [List.append_assoc] using hgen.symm
    obtain ⟨h1, _, h3⟩ :=
      eq_of_stateFree_prefix (stateFree_snoc hu rfl) (stateFree_pre c)
        (hsplit.trans (encode_eq c))
    rw [post] at h3
    obtain ⟨_, h5⟩ := List.cons.inj h3
    rcases pre_eq_snoc h1 with ⟨_, hz, _⟩ | ⟨m, a', hu', hz, _⟩
    · exact absurd hz (by simp)
    · have haa : a = a' := by injection hz
      exact ⟨⟨q, m.reverse, a', x :: c.right⟩, by
        rw [hu', h5, haa]; simp [encode, pre, post, List.append_assoc]⟩
  · -- move right at the marker
    have hsplit :
        (u ++ [Letter.tape a]) ++
          (Letter.state q' ::
            (Letter.tape default :: Letter.endR :: v)) = encode c := by
      simpa [List.append_assoc] using hgen.symm
    obtain ⟨h1, _, h3⟩ :=
      eq_of_stateFree_prefix (stateFree_snoc hu rfl) (stateFree_pre c)
        (hsplit.trans (encode_eq c))
    rw [post] at h3
    obtain ⟨_, h5⟩ := List.cons.inj h3
    rcases pre_eq_snoc h1 with ⟨_, hz, _⟩ | ⟨m, a', hu', hz, _⟩
    · exact absurd hz (by simp)
    · have haa : a = a' := by injection hz
      rcases post_eq_cons h5 with ⟨_, _, hv'⟩ | ⟨_, _, _, hz', _⟩
      · exact ⟨⟨q, m.reverse, a', []⟩, by
          rw [hu', hv', haa]; simp [encode, pre, post]⟩
      · exact absurd hz'.symm (by simp)
  · -- ordinary move left
    have hsplit :
        u ++ (Letter.state q' ::
          (Letter.tape y :: Letter.tape a :: v)) = encode c := by
      simpa using hgen.symm
    obtain ⟨h1, _, h3⟩ :=
      eq_of_stateFree_prefix hu (stateFree_pre c) (hsplit.trans (encode_eq c))
    rw [post] at h3
    obtain ⟨_, h5⟩ := List.cons.inj h3
    rcases post_eq_cons h5 with ⟨_, hz, _⟩ | ⟨a', r', _, hz, hv'⟩
    · exact absurd hz (by simp)
    · have haa : a = a' := by injection hz
      exact ⟨⟨q, y :: c.left, a', r'⟩, by
        rw [h1, hv', haa]; simp [encode, pre, post, List.append_assoc]⟩
  · -- move left at the marker
    have hsplit :
        (u ++ [Letter.endL]) ++
          (Letter.state q' ::
            (Letter.tape default :: Letter.tape a :: v)) = encode c := by
      simpa [List.append_assoc] using hgen.symm
    obtain ⟨h1, _, h3⟩ :=
      eq_of_stateFree_prefix (stateFree_snoc hu rfl) (stateFree_pre c)
        (hsplit.trans (encode_eq c))
    rw [post] at h3
    obtain ⟨_, h5⟩ := List.cons.inj h3
    rcases pre_eq_snoc h1 with ⟨hu', _, _⟩ | ⟨m, y', _, hz, _⟩
    · rcases post_eq_cons h5 with ⟨_, hz', _⟩ | ⟨a', r', _, hz', hv'⟩
      · exact absurd hz' (by simp)
      · have haa : a = a' := by injection hz'
        exact ⟨⟨q, [], a', r'⟩, by
          rw [hu', hv', haa]; simp [encode, pre, post]⟩
    · exact absurd hz (by simp)

/-- A rewriting step into a configuration starts at a configuration. -/
theorem step_closed_inv {R : RewriteSystem (Letter Γ Λ)} (hR : Presents M R)
    (c : Cfg Γ Λ) (w : List (Letter Γ Λ)) (hstep : Step R w (encode c)) :
    ∃ d, w = encode d := by
  generalize hgen : encode c = z at hstep
  cases hstep with
  | intro u v l r hmem => exact step_closed_inv_of_rule ((hR.mem_iff l r).mp hmem) hgen

/-! ## The simulation -/

/-- **A machine is simulated by a rewriting system presenting its rules.**  All
four `SimulationOn` conditions hold, so `SimulationOn.derives_iff` applies: two
configurations are equal in the presented monoid exactly when the machine drives
them to a common configuration. -/
def simulation {R : RewriteSystem (Letter Γ Λ)} (hR : Presents M R) :
    SimulationOn (Letter Γ Λ) (Cfg Γ Λ) where
  system := R
  encode := encode
  step := step M
  encode_injective := encode_injective
  step_sound := step_sound hR
  step_complete := step_complete hR
  step_closed_inv := step_closed_inv hR

/-- **Distinct halts stay distinct.**  Two halting configurations are equal in
the presented monoid only if they are the same configuration --- so the word
problem of this monoid decides which halting configuration the machine reaches.
This is the statement Post's theorem turns into undecidability once the machine
is universal. -/
theorem mk_eq_mk_iff_of_halts {R : RewriteSystem (Letter Γ Λ)}
    (hR : Presents M R) {c d : Cfg Γ Λ}
    (hc : step M c = none) (hd : step M d = none) :
    StringRewriting.mk R (encode c) = StringRewriting.mk R (encode d) ↔ c = d :=
  (simulation hR).mk_eq_mk_iff_of_halts hc hd

/-- Derivability between configurations is meeting of machine runs. -/
theorem derives_iff {R : RewriteSystem (Letter Γ Λ)} (hR : Presents M R)
    (c d : Cfg Γ Λ) :
    Derives R (encode c) (encode d) ↔
      ∃ e, Reach (step M) c e ∧ Reach (step M) d e :=
  (simulation hR).derives_iff c d

/-- A run puts its endpoints in the same class, with no halting hypothesis: a
machine step is a rewriting step, and rewriting steps are equalities. -/
theorem mk_eq_mk_of_reach {R : RewriteSystem (Letter Γ Λ)} (hR : Presents M R)
    {c d : Cfg Γ Λ} (h : Reach (step M) c d) :
    StringRewriting.mk R (encode c) = StringRewriting.mk R (encode d) :=
  StringRewriting.mk_eq_mk_iff.mpr (((simulation hR).reduces_of_reach h).derives)

/-- **The word problem is the reachability problem.**  Against a halting
configuration, equality in the presented monoid says exactly that the machine
run from `c` arrives there --- so an algorithm for this monoid's word problem is
an algorithm for the machine's reachability problem. -/
theorem mk_eq_mk_iff_reach_of_halts {R : RewriteSystem (Letter Γ Λ)}
    (hR : Presents M R) {c d : Cfg Γ Λ} (hd : step M d = none) :
    StringRewriting.mk R (encode c) = StringRewriting.mk R (encode d) ↔
      Reach (step M) c d :=
  (simulation hR).mk_eq_mk_iff_reach_of_halts hd

/-! ## The rule set, exhibited

`Presents` says *which* rules a system must have; it does not build one, so
nothing above rules out its rules forming an infinite list meeting the spec.
Here they are listed outright, by `flatMap` over state/symbol pairs, and since
`RewriteSystem.rules` is a `List` the presentation is then finite by
construction.

The enumerations of the state set and the tape alphabet are taken as *data*
rather than extracted from `Fintype`, because `Finset.toList` is noncomputable
and the whole point of listing the rules is that the list is computable.
`exists_presents` recovers the `Fintype` phrasing, at the cost of being a mere
existence claim. -/

section Finite

variable (M)

/-- The rules contributed by a single transition, given an enumeration `tapes`
of the tape alphabet.  An ordinary move rule names the symbol the head moves
onto, so each move transition contributes one rule per tape symbol --- plus the
single rule that materialises a blank at the marker. -/
def rulesFor (tapes : List Γ) (q : Λ) (a : Γ) : Option (Λ × Action Γ) →
    List (List (Letter Γ Λ) × List (Letter Γ Λ))
  | none => []
  | some (q', .write b) =>
      [([Letter.state q, Letter.tape a], [Letter.state q', Letter.tape b])]
  | some (q', .moveRight) =>
      ([Letter.state q, Letter.tape a, Letter.endR],
       [Letter.tape a, Letter.state q', Letter.tape default, Letter.endR]) ::
      tapes.map fun x =>
        ([Letter.state q, Letter.tape a, Letter.tape x],
         [Letter.tape a, Letter.state q', Letter.tape x])
  | some (q', .moveLeft) =>
      ([Letter.endL, Letter.state q, Letter.tape a],
       [Letter.endL, Letter.state q', Letter.tape default, Letter.tape a]) ::
      tapes.map fun y =>
        ([Letter.tape y, Letter.state q, Letter.tape a],
         [Letter.state q', Letter.tape y, Letter.tape a])

theorem mem_rulesFor {tapes : List Γ} (htapes : ∀ x : Γ, x ∈ tapes)
    {q : Λ} {a : Γ} {o : Option (Λ × Action Γ)} {l r : List (Letter Γ Λ)} :
    (l, r) ∈ rulesFor tapes q a o ↔
      (∃ q' b, o = some (q', .write b) ∧
          l = [Letter.state q, Letter.tape a] ∧
          r = [Letter.state q', Letter.tape b]) ∨
      (∃ q' x, o = some (q', .moveRight) ∧
          l = [Letter.state q, Letter.tape a, Letter.tape x] ∧
          r = [Letter.tape a, Letter.state q', Letter.tape x]) ∨
      (∃ q', o = some (q', .moveRight) ∧
          l = [Letter.state q, Letter.tape a, Letter.endR] ∧
          r = [Letter.tape a, Letter.state q', Letter.tape default,
            Letter.endR]) ∨
      (∃ q' y, o = some (q', .moveLeft) ∧
          l = [Letter.tape y, Letter.state q, Letter.tape a] ∧
          r = [Letter.state q', Letter.tape y, Letter.tape a]) ∨
      (∃ q', o = some (q', .moveLeft) ∧
          l = [Letter.endL, Letter.state q, Letter.tape a] ∧
          r = [Letter.endL, Letter.state q', Letter.tape default,
            Letter.tape a]) := by
  cases o with
  | none => simp [rulesFor]
  | some p =>
    obtain ⟨q', act⟩ := p
    cases act <;> simp [rulesFor, htapes] <;> aesop

/-- Every rule of the machine, as a finite list, given enumerations of the state
set and the tape alphabet. -/
def machineRules (states : List Λ) (tapes : List Γ) :
    List (List (Letter Γ Λ) × List (Letter Γ Λ)) :=
  states.flatMap fun q => tapes.flatMap fun a => rulesFor tapes q a (M q a)

/-- The finite rewriting system attached to a machine. -/
def machineSystem (states : List Λ) (tapes : List Γ) : RewriteSystem (Letter Γ Λ) :=
  ⟨machineRules M states tapes⟩

theorem presents_machineSystem {states : List Λ} {tapes : List Γ}
    (hstates : ∀ q : Λ, q ∈ states) (htapes : ∀ a : Γ, a ∈ tapes) :
    Presents M (machineSystem M states tapes) := by
  constructor
  intro l r
  simp only [machineSystem, machineRules, List.mem_flatMap, mem_rulesFor htapes]
  constructor
  · rintro ⟨q, -, a, -, (⟨q', b, h1, h2, h3⟩ | ⟨q', x, h1, h2, h3⟩ |
      ⟨q', h1, h2, h3⟩ | ⟨q', y, h1, h2, h3⟩ | ⟨q', h1, h2, h3⟩)⟩
    · exact Or.inl ⟨q, a, q', b, h1, h2, h3⟩
    · exact Or.inr (Or.inl ⟨q, a, x, q', h1, h2, h3⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨q, a, q', h1, h2, h3⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨q, a, y, q', h1, h2, h3⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨q, a, q', h1, h2, h3⟩)))
  · rintro (⟨q, a, q', b, h1, h2, h3⟩ | ⟨q, a, x, q', h1, h2, h3⟩ |
      ⟨q, a, q', h1, h2, h3⟩ | ⟨q, a, y, q', h1, h2, h3⟩ | ⟨q, a, q', h1, h2, h3⟩)
    · exact ⟨q, hstates q, a, htapes a, Or.inl ⟨q', b, h1, h2, h3⟩⟩
    · exact ⟨q, hstates q, a, htapes a, Or.inr (Or.inl ⟨q', x, h1, h2, h3⟩)⟩
    · exact ⟨q, hstates q, a, htapes a, Or.inr (Or.inr (Or.inl ⟨q', h1, h2, h3⟩))⟩
    · exact ⟨q, hstates q, a, htapes a,
        Or.inr (Or.inr (Or.inr (Or.inl ⟨q', y, h1, h2, h3⟩)))⟩
    · exact ⟨q, hstates q, a, htapes a,
        Or.inr (Or.inr (Or.inr (Or.inr ⟨q', h1, h2, h3⟩)))⟩

/-- **A machine with enumerated alphabets is simulated by an explicitly listed
finite rewriting system.** -/
def machineSimulation {states : List Λ} {tapes : List Γ}
    (hstates : ∀ q : Λ, q ∈ states) (htapes : ∀ a : Γ, a ∈ tapes) :
    SimulationOn (Letter Γ Λ) (Cfg Γ Λ) :=
  simulation (presents_machineSystem M hstates htapes)

/-- **The word problem of the listed system decides the machine's halting
configuration.**  Two halting configurations are equal in the presented monoid
exactly when they are the same configuration --- for the explicit finite rule
list above, and for a machine whose tape is genuinely unbounded. -/
theorem machineSystem_mk_eq_mk_iff {states : List Λ} {tapes : List Γ}
    (hstates : ∀ q : Λ, q ∈ states) (htapes : ∀ a : Γ, a ∈ tapes)
    {c d : Cfg Γ Λ} (hc : step M c = none) (hd : step M d = none) :
    StringRewriting.mk (machineSystem M states tapes) (encode c) =
      StringRewriting.mk (machineSystem M states tapes) (encode d) ↔ c = d :=
  mk_eq_mk_iff_of_halts (presents_machineSystem M hstates htapes) hc hd

/-- **The listed system's word problem is the machine's reachability problem.**
Everything here is explicit: the rules are a computable list, and equality of the
two words is exactly "the run from `c` reaches the halt `d`". -/
theorem machineSystem_mk_eq_mk_iff_reach {states : List Λ} {tapes : List Γ}
    (hstates : ∀ q : Λ, q ∈ states) (htapes : ∀ a : Γ, a ∈ tapes)
    {c d : Cfg Γ Λ} (hd : step M d = none) :
    StringRewriting.mk (machineSystem M states tapes) (encode c) =
      StringRewriting.mk (machineSystem M states tapes) (encode d) ↔
      Reach (step M) c d :=
  mk_eq_mk_iff_reach_of_halts (presents_machineSystem M hstates htapes) hd

/-- Derivability in the listed system is meeting of machine runs. -/
theorem machineSystem_derives_iff {states : List Λ} {tapes : List Γ}
    (hstates : ∀ q : Λ, q ∈ states) (htapes : ∀ a : Γ, a ∈ tapes)
    (c d : Cfg Γ Λ) :
    Derives (machineSystem M states tapes) (encode c) (encode d) ↔
      ∃ e, Reach (step M) c e ∧ Reach (step M) d e :=
  derives_iff (presents_machineSystem M hstates htapes) c d

/-- Finite alphabets always admit such enumerations, so every finite machine is
presented by a finite rewriting system. -/
theorem exists_presents [Fintype Γ] [Fintype Λ] :
    ∃ R : RewriteSystem (Letter Γ Λ), Presents M R :=
  ⟨machineSystem M (Finset.univ : Finset Λ).toList (Finset.univ : Finset Γ).toList,
    presents_machineSystem M (fun q => by simp) (fun a => by simp)⟩

end Finite

end PostMachine
end StringRewriting
end GroupApproximation
