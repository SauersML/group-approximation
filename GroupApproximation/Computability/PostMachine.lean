import GroupApproximation.Computability.RewriteSimulationOn

/-!
# A machine, simulated by a finite rewriting system

This is Post's construction, in the form `SimulationOn` consumes.

A deterministic machine with a two-way tape is encoded so that a configuration
becomes a word carrying exactly one state letter, and each transition becomes a
rewriting rule firing at that letter.  The four `SimulationOn` conditions are
discharged here, so `SimulationOn.derives_iff` applies: two configurations are
equal in the presented monoid exactly when the machine drives them to a common
one, and by `SimulationOn.eq_of_derives_of_halts` distinct halts stay distinct.

## The one lemma that does the work

Everything reduces to `eq_of_stateFree_prefix`: if two decompositions of a word
put a state letter at the head of their tails and have state-free prefixes, the
decompositions agree.  Every rule's left-hand side carries exactly one state
letter and a configuration word carries exactly one, so this pins *where* a rule
can fire.  The case analysis over "which occurrence matched" collapses before it
starts, which is the step that makes a machine simulation feasible at all.

The same fact gives backward closure: each rule has one state letter on both
sides, so a word rewriting *into* a configuration had one too.

## Scope

The machine halts when a move would run off its tape, so no tape-extension
rules are needed and halting configurations are automatically normal forms.
That keeps the rule set to three shapes.  Extending the tape at end markers is
additive and touches none of the proofs here.
-/

namespace GroupApproximation
namespace StringRewriting
namespace PostMachine

/-- Letters of the encoding alphabet: tape symbols and state symbols. -/
inductive Letter (Γ Λ : Type) where
  | tape : Γ → Letter Γ Λ
  | state : Λ → Letter Γ Λ
  deriving DecidableEq

/-- What a transition does. -/
inductive Action (Γ : Type) where
  | write : Γ → Action Γ
  | moveLeft : Action Γ
  | moveRight : Action Γ
  deriving DecidableEq

/-- A deterministic machine. -/
abbrev Machine (Γ Λ : Type) := Λ → Γ → Option (Λ × Action Γ)

/-- A configuration: state, tape left of the head (nearest first), the scanned
symbol, and tape right of the head. -/
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

@[simp] theorem isState_tape (a : Γ) :
    isState (Letter.tape a : Letter Γ Λ) = false := rfl

@[simp] theorem isState_state (q : Λ) :
    isState (Letter.state q : Letter Γ Λ) = true := rfl

/-- A word is state-free when none of its letters is a state letter. -/
def StateFree (w : List (Letter Γ Λ)) : Prop := ∀ x ∈ w, isState x = false

theorem stateFree_map_tape (l : List Γ) :
    StateFree (l.map (Letter.tape : Γ → Letter Γ Λ)) := by
  intro x hx
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
  rfl

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

/-! ## The machine and its encoding -/

variable (M : Machine Γ Λ)

/-- One machine step.  A move that would run off the tape halts. -/
def step : Cfg Γ Λ → Option (Cfg Γ Λ) := fun c =>
  match M c.q c.head with
  | none => none
  | some (q', .write b) => some { q := q', left := c.left, head := b, right := c.right }
  | some (q', .moveRight) =>
      match c.right with
      | [] => none
      | x :: r => some { q := q', left := c.head :: c.left, head := x, right := r }
  | some (q', .moveLeft) =>
      match c.left with
      | [] => none
      | y :: l => some { q := q', left := l, head := y, right := c.head :: c.right }

/-- A configuration as a word. -/
def encode (c : Cfg Γ Λ) : List (Letter Γ Λ) :=
  c.left.reverse.map Letter.tape ++
    (Letter.state c.q :: Letter.tape c.head :: c.right.map Letter.tape)

theorem countP_encode (c : Cfg Γ Λ) :
    (encode c).countP (isState : Letter Γ Λ → Bool) = 1 := by
  simp [encode]

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

theorem encode_injective : Function.Injective (encode : Cfg Γ Λ → _) := by
  intro c d h
  obtain ⟨h1, h2, h3⟩ :=
    eq_of_stateFree_prefix (stateFree_map_tape _) (stateFree_map_tape _) h
  obtain ⟨hh, hr⟩ := List.cons.inj h3
  have hhead : c.head = d.head := by injection hh
  have hleft : c.left = d.left := by
    have := map_tape_injective h1
    simpa using congrArg List.reverse this
  have hright : c.right = d.right := map_tape_injective hr
  cases c; cases d
  simp_all

/-! ## The rules -/

/-- The three rule shapes.  Every left-hand side carries exactly one state
letter, and so does every right-hand side; that single fact is what makes both
closure conditions work. -/
def IsMachineRule (l r : List (Letter Γ Λ)) : Prop :=
  (∃ q a q' b, M q a = some (q', .write b) ∧
      l = [Letter.state q, Letter.tape a] ∧
      r = [Letter.state q', Letter.tape b]) ∨
  (∃ q a x q', M q a = some (q', .moveRight) ∧
      l = [Letter.state q, Letter.tape a, Letter.tape x] ∧
      r = [Letter.tape a, Letter.state q', Letter.tape x]) ∨
  (∃ q a y q', M q a = some (q', .moveLeft) ∧
      l = [Letter.tape y, Letter.state q, Letter.tape a] ∧
      r = [Letter.state q', Letter.tape y, Letter.tape a])

/-- A rewriting system presenting exactly the machine's rules. -/
structure Presents (R : RewriteSystem (Letter Γ Λ)) : Prop where
  mem_iff : ∀ l r, (l, r) ∈ R.rules ↔ IsMachineRule M l r

variable {M}

theorem countP_lhs {l r : List (Letter Γ Λ)} (h : IsMachineRule M l r) :
    l.countP isState = 1 := by
  rcases h with ⟨q, a, q', b, _, rfl, _⟩ | ⟨q, a, x, q', _, rfl, _⟩ |
    ⟨q, a, y, q', _, rfl, _⟩ <;> simp

theorem countP_rhs {l r : List (Letter Γ Λ)} (h : IsMachineRule M l r) :
    r.countP isState = 1 := by
  rcases h with ⟨q, a, q', b, _, _, rfl⟩ | ⟨q, a, x, q', _, _, rfl⟩ |
    ⟨q, a, y, q', _, _, rfl⟩ <;> simp

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

/-- Reading a mapped tape word off a cons. -/
theorem map_tape_eq_cons {l : List Γ} {x : Γ} {v : List (Letter Γ Λ)}
    (h : l.map Letter.tape = Letter.tape x :: v) :
    ∃ r, l = x :: r ∧ v = r.map Letter.tape := by
  cases l with
  | nil => simp at h
  | cons a l =>
    simp only [List.map_cons] at h
    obtain ⟨h1, h2⟩ := List.cons.inj h
    have : a = x := by injection h1
    exact ⟨l, by rw [this], h2.symm⟩

/-- Reading a mapped tape word off a snoc. -/
theorem map_tape_eq_snoc {l : List Γ} {y : Γ} {u : List (Letter Γ Λ)}
    (h : u ++ [Letter.tape y] = l.map Letter.tape) :
    ∃ m, l = m ++ [y] ∧ u = m.map Letter.tape := by
  induction l generalizing u with
  | nil => simp at h
  | cons a l ih =>
    cases u with
    | nil =>
      simp only [List.nil_append, List.map_cons] at h
      obtain ⟨h1, h2⟩ := List.cons.inj h
      have hay : y = a := by injection h1
      have : l = [] := by simpa using h2.symm
      exact ⟨[], by simp [this, hay], rfl⟩
    | cons z u =>
      simp only [List.cons_append, List.map_cons] at h
      obtain ⟨h1, h2⟩ := List.cons.inj h
      obtain ⟨m, hm1, hm2⟩ := ih h2
      exact ⟨a :: m, by simp [hm1], by simp [h1, hm2]⟩

/-! ## Soundness: a machine step is a rewriting step -/

theorem step_sound {R : RewriteSystem (Letter Γ Λ)} (hR : Presents M R)
    (c d : Cfg Γ Λ) (h : step M c = some d) : Step R (encode c) (encode d) := by
  unfold step at h
  cases hM : M c.q c.head with
  | none => rw [hM] at h; exact absurd h (by simp)
  | some p =>
    obtain ⟨q', act⟩ := p
    rw [hM] at h
    cases act with
    | write b =>
      simp only [Option.some.injEq] at h
      subst h
      have hrule : IsMachineRule M [Letter.state c.q, Letter.tape c.head]
          [Letter.state q', Letter.tape b] :=
        Or.inl ⟨c.q, c.head, q', b, hM, rfl, rfl⟩
      have hs := Step.intro (R := R) (c.left.reverse.map Letter.tape)
        (c.right.map Letter.tape) [Letter.state c.q, Letter.tape c.head]
        [Letter.state q', Letter.tape b] ((hR.mem_iff _ _).mpr hrule)
      simpa [encode, List.append_assoc] using hs
    | moveRight =>
      cases hr : c.right with
      | nil => rw [hr] at h; exact absurd h (by simp)
      | cons x r =>
        rw [hr] at h
        simp only [Option.some.injEq] at h
        subst h
        have hrule : IsMachineRule M
            [Letter.state c.q, Letter.tape c.head, Letter.tape x]
            [Letter.tape c.head, Letter.state q', Letter.tape x] :=
          Or.inr (Or.inl ⟨c.q, c.head, x, q', hM, rfl, rfl⟩)
        have hs := Step.intro (R := R) (c.left.reverse.map Letter.tape)
          (r.map Letter.tape)
          [Letter.state c.q, Letter.tape c.head, Letter.tape x]
          [Letter.tape c.head, Letter.state q', Letter.tape x]
          ((hR.mem_iff _ _).mpr hrule)
        simpa [encode, hr, List.append_assoc] using hs
    | moveLeft =>
      cases hl : c.left with
      | nil => rw [hl] at h; exact absurd h (by simp)
      | cons y l =>
        rw [hl] at h
        simp only [Option.some.injEq] at h
        subst h
        have hrule : IsMachineRule M
            [Letter.tape y, Letter.state c.q, Letter.tape c.head]
            [Letter.state q', Letter.tape y, Letter.tape c.head] :=
          Or.inr (Or.inr ⟨c.q, c.head, y, q', hM, rfl, rfl⟩)
        have hs := Step.intro (R := R) (l.reverse.map Letter.tape)
          (c.right.map Letter.tape)
          [Letter.tape y, Letter.state c.q, Letter.tape c.head]
          [Letter.state q', Letter.tape y, Letter.tape c.head]
          ((hR.mem_iff _ _).mpr hrule)
        simpa [encode, hl, List.append_assoc] using hs

/-! ## Completeness: a rewriting step out of a configuration is a machine step -/

theorem step_complete {R : RewriteSystem (Letter Γ Λ)} (hR : Presents M R)
    (c : Cfg Γ Λ) (w : List (Letter Γ Λ)) (hstep : Step R (encode c) w) :
    ∃ d, step M c = some d ∧ w = encode d := by
  generalize hgen : encode c = z at hstep
  cases hstep with
  | intro u v l r hmem =>
    have hrule := (hR.mem_iff l r).mp hmem
    obtain ⟨hu, hv⟩ := stateFree_context (c := c) hgen.symm (countP_lhs hrule)
    rcases hrule with ⟨q, a, q', b, hM, rfl, rfl⟩ | ⟨q, a, x, q', hM, rfl, rfl⟩ |
      ⟨q, a, y, q', hM, rfl, rfl⟩
    · -- write
      have hsplit : u ++ (Letter.state q :: (Letter.tape a :: v)) = encode c := by
        simpa [List.append_assoc] using hgen.symm
      obtain ⟨h1, h2, h3⟩ :=
        eq_of_stateFree_prefix hu (stateFree_map_tape _) hsplit
      obtain ⟨h4, h5⟩ := List.cons.inj h3
      have ha : a = c.head := by injection h4
      subst h2; subst ha
      refine ⟨{ q := q', left := c.left, head := b, right := c.right }, ?_, ?_⟩
      · unfold step; rw [hM]
      · rw [h1, h5]; simp [encode, List.append_assoc]
    · -- move right
      have hsplit : u ++ (Letter.state q ::
          (Letter.tape a :: Letter.tape x :: v)) = encode c := by
        simpa [List.append_assoc] using
          hgen.symm
      obtain ⟨h1, h2, h3⟩ :=
        eq_of_stateFree_prefix hu (stateFree_map_tape _) hsplit
      obtain ⟨h4, h5⟩ := List.cons.inj h3
      have ha : a = c.head := by injection h4
      subst h2; subst ha
      obtain ⟨r0, hr0, hv0⟩ := map_tape_eq_cons h5.symm
      refine ⟨{ q := q', left := c.head :: c.left, head := x, right := r0 }, ?_, ?_⟩
      · unfold step; rw [hM, hr0]
      · rw [h1, hv0]; simp [encode, List.append_assoc]
    · -- move left
      have hsplit : (u ++ [Letter.tape y]) ++
          (Letter.state q :: (Letter.tape a :: v)) = encode c := by
        simpa [List.append_assoc] using
          hgen.symm
      have huy : StateFree (u ++ [Letter.tape y]) := by
        intro z hz
        rcases List.mem_append.mp hz with h | h
        · exact hu z h
        · simp at h; rw [h]; rfl
      obtain ⟨h1, h2, h3⟩ :=
        eq_of_stateFree_prefix huy (stateFree_map_tape _) hsplit
      obtain ⟨h4, h5⟩ := List.cons.inj h3
      have ha : a = c.head := by injection h4
      subst h2; subst ha
      obtain ⟨m, hm1, hm2⟩ := map_tape_eq_snoc h1
      have hleft : c.left = y :: m.reverse := by
        have := congrArg List.reverse hm1
        simpa using this
      refine ⟨{ q := q', left := m.reverse, head := y,
                right := c.head :: c.right }, ?_, ?_⟩
      · unfold step; rw [hM, hleft]
      · rw [hm2, h5]; simp [encode, List.append_assoc]

/-! ## Backward closure -/

theorem step_closed_inv {R : RewriteSystem (Letter Γ Λ)} (hR : Presents M R)
    (c : Cfg Γ Λ) (w : List (Letter Γ Λ)) (hstep : Step R w (encode c)) :
    ∃ d, w = encode d := by
  generalize hgen : encode c = z at hstep
  cases hstep with
  | intro u v l r hmem =>
    have hrule := (hR.mem_iff l r).mp hmem
    obtain ⟨hu, hv⟩ := stateFree_context (c := c) hgen.symm (countP_rhs hrule)
    rcases hrule with ⟨q, a, q', b, hM, rfl, rfl⟩ | ⟨q, a, x, q', hM, rfl, rfl⟩ |
      ⟨q, a, y, q', hM, rfl, rfl⟩
    · -- write: the right-hand side sits exactly where the state letter is
      have hsplit : u ++ (Letter.state q' :: (Letter.tape b :: v)) = encode c := by
        simpa [List.append_assoc] using
          hgen.symm
      obtain ⟨h1, _, h3⟩ :=
        eq_of_stateFree_prefix hu (stateFree_map_tape _) hsplit
      obtain ⟨_, h5⟩ := List.cons.inj h3
      exact ⟨{ q := q, left := c.left, head := a, right := c.right },
        by rw [h1, h5]; simp [encode, List.append_assoc]⟩
    · -- move right: its right-hand side has the state letter one place along
      have hsplit : (u ++ [Letter.tape a]) ++
          (Letter.state q' :: (Letter.tape x :: v)) = encode c := by
        simpa [List.append_assoc] using
          hgen.symm
      have hua : StateFree (u ++ [Letter.tape a]) := by
        intro z hz
        rcases List.mem_append.mp hz with h | h
        · exact hu z h
        · simp at h; rw [h]; rfl
      obtain ⟨h1, _, h3⟩ :=
        eq_of_stateFree_prefix hua (stateFree_map_tape _) hsplit
      obtain ⟨h4, h5⟩ := List.cons.inj h3
      have hx : x = c.head := by injection h4
      obtain ⟨m, hm1, hm2⟩ := map_tape_eq_snoc h1
      refine ⟨{ q := q, left := m.reverse, head := a,
                right := x :: c.right }, ?_⟩
      rw [hm2, h5, hx]
      simp [encode, List.append_assoc]
    · -- move left: its right-hand side has the state letter at the front
      have hsplit : u ++ (Letter.state q' ::
          (Letter.tape y :: Letter.tape a :: v)) = encode c := by
        simpa [List.append_assoc] using
          hgen.symm
      obtain ⟨h1, _, h3⟩ :=
        eq_of_stateFree_prefix hu (stateFree_map_tape _) hsplit
      obtain ⟨h4, h5⟩ := List.cons.inj h3
      have hy : y = c.head := by injection h4
      obtain ⟨r0, hr0, hv0⟩ := map_tape_eq_cons h5.symm
      refine ⟨{ q := q, left := y :: c.left, head := a, right := r0 }, ?_⟩
      rw [h1, hv0]
      simp [encode, List.append_assoc]

/-! ## The simulation -/

/-- **A deterministic machine is simulated by a finite rewriting system.**  All
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

/-! ## The rule set, exhibited

`Presents` says *which* rules a system must have; it does not build one.  Here
the rules are listed outright, by `flatMap` over state/symbol pairs, and since
`RewriteSystem.rules` is a `List` the resulting presentation is finite by
construction --- there is nothing further to check.

The enumerations of the state set and tape alphabet are taken as *data* rather
than extracted from `Fintype`, because `Finset.toList` is noncomputable and the
whole point of listing the rules is that the list is computable.  `exists_presents`
recovers the `Fintype` phrasing, at the cost of being a mere existence claim. -/

section Finite

variable (M)

/-- The rules contributed by a single transition, given an enumeration `tapes`
of the tape alphabet.  A move rule has to name the symbol the head moves onto,
so each move transition contributes one rule per tape symbol. -/
def rulesFor (tapes : List Γ) (q : Λ) (a : Γ) : Option (Λ × Action Γ) →
    List (List (Letter Γ Λ) × List (Letter Γ Λ))
  | none => []
  | some (q', .write b) =>
      [([Letter.state q, Letter.tape a], [Letter.state q', Letter.tape b])]
  | some (q', .moveRight) =>
      tapes.map fun x =>
        ([Letter.state q, Letter.tape a, Letter.tape x],
         [Letter.tape a, Letter.state q', Letter.tape x])
  | some (q', .moveLeft) =>
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
      (∃ q' y, o = some (q', .moveLeft) ∧
          l = [Letter.tape y, Letter.state q, Letter.tape a] ∧
          r = [Letter.state q', Letter.tape y, Letter.tape a]) := by
  cases o with
  | none => simp [rulesFor]
  | some p =>
    obtain ⟨q', act⟩ := p
    cases act <;> simp [rulesFor, htapes] <;>
      exact ⟨fun ⟨x, h1, h2⟩ => ⟨x, h1.symm, h2.symm⟩,
             fun ⟨x, h1, h2⟩ => ⟨x, h1.symm, h2.symm⟩⟩

/-- Every rule of the machine, as a finite list, given enumerations of the
state set and the tape alphabet. -/
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
      ⟨q', y, h1, h2, h3⟩)⟩
    · exact Or.inl ⟨q, a, q', b, h1, h2, h3⟩
    · exact Or.inr (Or.inl ⟨q, a, x, q', h1, h2, h3⟩)
    · exact Or.inr (Or.inr ⟨q, a, y, q', h1, h2, h3⟩)
  · rintro (⟨q, a, q', b, h1, h2, h3⟩ | ⟨q, a, x, q', h1, h2, h3⟩ |
      ⟨q, a, y, q', h1, h2, h3⟩)
    · exact ⟨q, hstates q, a, htapes a, Or.inl ⟨q', b, h1, h2, h3⟩⟩
    · exact ⟨q, hstates q, a, htapes a, Or.inr (Or.inl ⟨q', x, h1, h2, h3⟩)⟩
    · exact ⟨q, hstates q, a, htapes a, Or.inr (Or.inr ⟨q', y, h1, h2, h3⟩)⟩

/-- **A machine with enumerated alphabets is simulated by an explicitly listed
finite rewriting system.** -/
def machineSimulation {states : List Λ} {tapes : List Γ}
    (hstates : ∀ q : Λ, q ∈ states) (htapes : ∀ a : Γ, a ∈ tapes) :
    SimulationOn (Letter Γ Λ) (Cfg Γ Λ) :=
  simulation (presents_machineSystem M hstates htapes)

/-- **The word problem of the listed system decides the machine's halting
configuration.**  Two halting configurations are equal in the presented monoid
exactly when they are the same configuration --- unconditionally, for the
explicit finite rule list above. -/
theorem machineSystem_mk_eq_mk_iff {states : List Λ} {tapes : List Γ}
    (hstates : ∀ q : Λ, q ∈ states) (htapes : ∀ a : Γ, a ∈ tapes)
    {c d : Cfg Γ Λ} (hc : step M c = none) (hd : step M d = none) :
    StringRewriting.mk (machineSystem M states tapes) (encode c) =
      StringRewriting.mk (machineSystem M states tapes) (encode d) ↔ c = d :=
  mk_eq_mk_iff_of_halts (presents_machineSystem M hstates htapes) hc hd

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
