import GroupApproximation.Computability.SemigroupWordProblemMachine

/-!
# The simulation: a machine halts iff two words become equal

This file proves both directions of the Markov--Post simulation for the machine
model and the rewriting system of `SemigroupWordProblemMachine`:

`halts_iff_thueEquiv` : `M.Halts c ↔ ThueEquiv … (encCfg M c) [Letter.done]`.

The forward direction is the routine one: a halting computation is turned into
a chain of rewrites (`derives_of_machine_chain`), and the halting configuration
is then erased letter by letter down to the single letter `done`
(`derives_done_of_eraseWord`).

The backward direction is the one that carries content.  A Thue equivalence is
an arbitrary zig-zag, and it is turned into a one-directional derivation by
`thueEquiv_iff_derives`, which is available because `[Letter.done]` is a normal
form (`done_normalForm`) and because rewriting is deterministic on words of
weight one (`Step.det`, via `machine_isLocal`).  A one-directional derivation
out of a configuration word is then followed by `orbit`: as long as the machine
has not halted, the *unique* rewrite available reproduces the encoding of the
next configuration, so every word reachable from `encCfg M c` is an encoded
configuration, and no encoded configuration is the one-letter word `done`.

None of this is conditional and none of it is a manuscript statement; see
`SemigroupWordProblem.lean` for what remains to be done before Markov--Post
itself, and `AdianRabinMarkovProperty.lean` for the manuscript context.
-/

namespace GroupApproximation
namespace SemigroupWordProblem

open Relation

section Simulation

variable {Γ Λ : Type}

/-! ## Encoding configurations as words -/

/-- The word `endL · reverse l · q · b · v · endR`: the general shape of an
encoded configuration, with `l` the tape left of the head (nearest cell first),
`b` the scanned cell and `v` the tape strictly right of it. -/
def word (l : List Γ) (q : Λ) (b : Γ) (v : List Γ) : List (Letter Γ Λ) :=
  (Letter.endL :: (l.reverse.map Letter.tape)) ++
    (Letter.state q :: (Letter.tape b :: (v.map Letter.tape ++ [Letter.endR])))

/-- The word encoding a configuration. -/
def encCfg (M : Machine Γ Λ) (c : Cfg Γ Λ) : List (Letter Γ Λ) :=
  word c.left c.state (M.scan c.right) (tapeRest c.right)

/-- The word reached immediately after the machine halts: the state letter has
become the right-travelling eraser and the scanned cell is gone. -/
def eraseWord (l : List Γ) (v : List Γ) : List (Letter Γ Λ) :=
  (Letter.endL :: (l.reverse.map Letter.tape)) ++
    (Letter.eraseR :: (v.map Letter.tape ++ [Letter.endR]))

/-- The part of an encoded word strictly left of the letter adjacent to the
head. -/
def leftPart : List Γ → List (Letter Γ Λ)
  | [] => []
  | _ :: l => Letter.endL :: (l.reverse.map Letter.tape)

/-- The part of an encoded word strictly right of the letter following the
scanned cell. -/
def rightPart : List Γ → List (Letter Γ Λ)
  | [] => []
  | _ :: l => (l.map Letter.tape) ++ [Letter.endR]

/-- **The redex decomposition.**  An encoded configuration word is a left
context, a four-letter machine redex, and a right context. -/
theorem word_eq_redex (l : List Γ) (q : Λ) (b : Γ) (v : List Γ) :
    word l q b v =
      leftPart l ++ lhsWord ruleSp rulePre rulePost
        (RIdx.mach (headOpt l) q b (headOpt v)) ++ rightPart v := by
  cases l <;> cases v <;>
    simp [word, leftPart, rightPart, headOpt, optL, optR, lhsWord, rulePre, rulePost,
      ruleSp, List.reverse_cons, List.map_append]

/-- The result of firing a right-moving machine rule is the encoding of the
next configuration. -/
theorem word_right_move (M : Machine Γ Λ) (l : List Γ) (q : Λ) (b : Γ) (v : List Γ) :
    leftPart l ++ ([optL (headOpt l), Letter.tape b, Letter.state q] ++
        rightTail M.blank (headOpt v)) ++ rightPart v
      = word (b :: l) q (M.scan v) (tapeRest v) := by
  cases l <;> cases v <;>
    simp [word, leftPart, rightPart, headOpt, optL, rightTail, tapeRest,
      Machine.scan, List.reverse_cons, List.map_append]

/-- The result of firing a left-moving machine rule is the encoding of the next
configuration. -/
theorem word_left_move (M : Machine Γ Λ) (l : List Γ) (q : Λ) (b : Γ) (v : List Γ) :
    leftPart l ++ (leftHead M.blank q (headOpt l) ++
        [Letter.tape b, optR (headOpt v)]) ++ rightPart v
      = word (tapeRest l) q (M.scan l) (b :: v) := by
  cases l <;> cases v <;>
    simp [word, leftPart, rightPart, headOpt, optR, leftHead, tapeRest,
      Machine.scan]

/-- The result of firing a halting machine rule is the eraser word. -/
theorem word_halt (l : List Γ) (v : List Γ) :
    leftPart l ++ [optL (headOpt l), Letter.eraseR, optR (headOpt v)] ++ rightPart v
      = (eraseWord l v : List (Letter Γ Λ)) := by
  cases l <;> cases v <;>
    simp [eraseWord, leftPart, rightPart, headOpt, optL, optR, List.reverse_cons,
      List.map_append]

/-! ## One machine step is one rewrite -/

/-- **Forward simulation, one step.**  A machine step becomes a single rewrite
between the encoded configurations. -/
theorem sstep_of_machine_step (M : Machine Γ Λ) {c c' : Cfg Γ Λ} (h : M.Step c c') :
    Step ruleSp rulePre rulePost (ruleRhs M) (encCfg M c) (encCfg M c') := by
  rcases h with ⟨q, b, htr, rfl⟩ | ⟨q, b, htr, rfl⟩
  · refine ⟨RIdx.mach (headOpt c.left) c.state (M.scan c.right)
      (headOpt (tapeRest c.right)), leftPart c.left, rightPart (tapeRest c.right), ?_, ?_⟩
    · exact word_eq_redex c.left c.state (M.scan c.right) (tapeRest c.right)
    · have hr : ruleRhs M (RIdx.mach (headOpt c.left) c.state (M.scan c.right)
            (headOpt (tapeRest c.right)))
          = [optL (headOpt c.left), Letter.tape b, Letter.state q] ++
              rightTail M.blank (headOpt (tapeRest c.right)) := by
        show machRhsOf M.blank (headOpt c.left) (headOpt (tapeRest c.right))
            (M.trans c.state (M.scan c.right)) = _
        rw [htr]
        rfl
      rw [hr]
      exact (word_right_move M c.left q b (tapeRest c.right)).symm
  · refine ⟨RIdx.mach (headOpt c.left) c.state (M.scan c.right)
      (headOpt (tapeRest c.right)), leftPart c.left, rightPart (tapeRest c.right), ?_, ?_⟩
    · exact word_eq_redex c.left c.state (M.scan c.right) (tapeRest c.right)
    · have hr : ruleRhs M (RIdx.mach (headOpt c.left) c.state (M.scan c.right)
            (headOpt (tapeRest c.right)))
          = leftHead M.blank q (headOpt c.left) ++
              [Letter.tape b, optR (headOpt (tapeRest c.right))] := by
        show machRhsOf M.blank (headOpt c.left) (headOpt (tapeRest c.right))
            (M.trans c.state (M.scan c.right)) = _
        rw [htr]
        rfl
      rw [hr]
      exact (word_left_move M c.left q b (tapeRest c.right)).symm

/-- **The halting step.**  A halting configuration rewrites to the eraser
word. -/
theorem sstep_of_halted (M : Machine Γ Λ) {c : Cfg Γ Λ} (h : M.Halted c) :
    Step ruleSp rulePre rulePost (ruleRhs M) (encCfg M c)
      (eraseWord c.left (tapeRest c.right)) := by
  have h' : M.trans c.state (M.scan c.right) = none := h
  refine ⟨RIdx.mach (headOpt c.left) c.state (M.scan c.right)
    (headOpt (tapeRest c.right)), leftPart c.left, rightPart (tapeRest c.right), ?_, ?_⟩
  · exact word_eq_redex c.left c.state (M.scan c.right) (tapeRest c.right)
  · have hr : ruleRhs M (RIdx.mach (headOpt c.left) c.state (M.scan c.right)
          (headOpt (tapeRest c.right)))
        = [optL (headOpt c.left), Letter.eraseR, optR (headOpt (tapeRest c.right))] := by
      show machRhsOf M.blank (headOpt c.left) (headOpt (tapeRest c.right))
          (M.trans c.state (M.scan c.right)) = _
      rw [h']
      rfl
    rw [hr]
    exact (word_halt c.left (tapeRest c.right)).symm

/-! ## The cleanup derivation -/

/-- Phase one of the cleanup: the right-travelling eraser deletes every tape
letter to its right. -/
theorem derives_eatRight (M : Machine Γ Λ) (v : List Γ) :
    ∀ (x y : List (Letter Γ Λ)),
      Derives ruleSp rulePre rulePost (ruleRhs M)
        (x ++ (Letter.eraseR :: (v.map Letter.tape ++ y)))
        (x ++ (Letter.eraseR :: y)) := by
  induction v with
  | nil => intro x y; exact ReflTransGen.refl
  | cons d t ih =>
      intro x y
      refine ReflTransGen.head ?_ (ih x y)
      refine ⟨RIdx.eatTapeR d, x, t.map Letter.tape ++ y, ?_, ?_⟩
      · simp [lhsWord, ruleSp, rulePre, rulePost]
      · simp [ruleRhs]

/-- Phase two of the cleanup: the left-travelling eraser deletes every tape
letter to its left. -/
theorem derives_eatLeft (M : Machine Γ Λ) (u : List Γ) :
    ∀ (x y : List (Letter Γ Λ)),
      Derives ruleSp rulePre rulePost (ruleRhs M)
        (x ++ (u.map Letter.tape ++ (Letter.eraseL :: y)))
        (x ++ (Letter.eraseL :: y)) := by
  induction u with
  | nil => intro x y; exact ReflTransGen.refl
  | cons d t ih =>
      intro x y
      have e1 : x ++ ((d :: t).map Letter.tape ++ (Letter.eraseL :: y))
          = (x ++ [Letter.tape d]) ++ (t.map Letter.tape ++ (Letter.eraseL :: y)) := by
        simp [List.append_assoc]
      rw [e1]
      refine ReflTransGen.trans (ih (x ++ [Letter.tape d]) y) ?_
      refine ReflTransGen.single ⟨RIdx.eatTapeL d, x, y, ?_, ?_⟩
      · simp [lhsWord, ruleSp, rulePre, rulePost, List.append_assoc]
      · simp [ruleRhs]

/-- **The cleanup.**  The eraser word derives the single letter `done`. -/
theorem derives_done_of_eraseWord (M : Machine Γ Λ) (l v : List Γ) :
    Derives ruleSp rulePre rulePost (ruleRhs M) (eraseWord l v) [Letter.done] := by
  have h1 : Derives ruleSp rulePre rulePost (ruleRhs M) (eraseWord l v)
      ((Letter.endL :: (l.reverse.map Letter.tape)) ++ (Letter.eraseR :: [Letter.endR])) :=
    derives_eatRight M v (Letter.endL :: (l.reverse.map Letter.tape)) [Letter.endR]
  have h2 : Step ruleSp rulePre rulePost (ruleRhs M)
      ((Letter.endL :: (l.reverse.map Letter.tape)) ++ (Letter.eraseR :: [Letter.endR]))
      ((Letter.endL :: (l.reverse.map Letter.tape)) ++ (Letter.eraseL :: [])) := by
    refine ⟨RIdx.eatEndR, Letter.endL :: (l.reverse.map Letter.tape), [], ?_, ?_⟩
    · simp [lhsWord, ruleSp, rulePre, rulePost]
    · simp [ruleRhs]
  have h3 : Derives ruleSp rulePre rulePost (ruleRhs M)
      ((Letter.endL :: (l.reverse.map Letter.tape)) ++ (Letter.eraseL :: []))
      (([Letter.endL] : List (Letter Γ Λ)) ++ (Letter.eraseL :: [])) :=
    derives_eatLeft M l.reverse [Letter.endL] []
  have h4 : Step ruleSp rulePre rulePost (ruleRhs M)
      (([Letter.endL] : List (Letter Γ Λ)) ++ (Letter.eraseL :: [])) [Letter.done] := by
    refine ⟨RIdx.eatEndL, [], [], ?_, ?_⟩
    · simp [lhsWord, ruleSp, rulePre, rulePost]
    · simp [ruleRhs]
  exact ReflTransGen.trans h1
    (ReflTransGen.trans (ReflTransGen.single h2) (ReflTransGen.trans h3 (ReflTransGen.single h4)))

/-! ## Both directions of the simulation -/

/-- Every encoded configuration has weight one, so rewriting is deterministic
on the whole forward orbit of an encoded configuration. -/
@[simp] theorem weight_encCfg (M : Machine Γ Λ) (c : Cfg Γ Λ) :
    weight Letter.wt (encCfg M c) = 1 := by
  -- `List.map_reverse` would push the `reverse` outside the `map`, past the
  -- shape `weight_map_tape` recognises; the tape letters are what has weight
  -- zero, whichever order they are written in.
  simp [encCfg, word, Letter.wt, -List.map_reverse]

/-- No encoded configuration is the one-letter word `done`. -/
theorem encCfg_ne_done (M : Machine Γ Λ) (c : Cfg Γ Λ) :
    encCfg M c ≠ [Letter.done] := by
  intro h
  have hlen := congrArg List.length h
  simp only [encCfg, word, List.length_append, List.length_cons, List.length_nil,
    List.length_map, List.length_reverse] at hlen
  omega

/-- A halted configuration derives `done`. -/
theorem derives_done_of_halted (M : Machine Γ Λ) {c : Cfg Γ Λ} (h : M.Halted c) :
    Derives ruleSp rulePre rulePost (ruleRhs M) (encCfg M c) [Letter.done] :=
  ReflTransGen.head (sstep_of_halted M h) (derives_done_of_eraseWord M c.left (tapeRest c.right))

/-- A run of the machine becomes a derivation between the encoded
configurations. -/
theorem derives_of_machine_chain (M : Machine Γ Λ) {c c' : Cfg Γ Λ}
    (h : ReflTransGen M.Step c c') :
    Derives ruleSp rulePre rulePost (ruleRhs M) (encCfg M c) (encCfg M c') := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail hd hstep ih => exact ReflTransGen.tail ih (sstep_of_machine_step M hstep)

/-- **Forward direction.**  If the machine halts, the encoded configuration
derives `done`. -/
theorem derives_done_of_halts (M : Machine Γ Λ) {c : Cfg Γ Λ} (h : M.Halts c) :
    Derives ruleSp rulePre rulePost (ruleRhs M) (encCfg M c) [Letter.done] := by
  obtain ⟨c', hch, hhalt⟩ := h
  exact ReflTransGen.trans (derives_of_machine_chain M hch) (derives_done_of_halted M hhalt)

/-- **The orbit lemma.**  As long as the machine does not halt, every word
derivable from an encoded configuration is itself an encoded configuration --
the encoding of a configuration the machine actually reaches.  This is where
determinism of the rewriting system is used. -/
theorem orbit (M : Machine Γ Λ) {c : Cfg Γ Λ} (h : ¬ M.Halts c)
    {u : List (Letter Γ Λ)}
    (hd : Derives ruleSp rulePre rulePost (ruleRhs M) (encCfg M c) u) :
    ∃ c₁, ReflTransGen M.Step c c₁ ∧ u = encCfg M c₁ := by
  induction hd with
  | refl => exact ⟨c, ReflTransGen.refl, rfl⟩
  | tail hd' hstep ih =>
      obtain ⟨c₁, hch, rfl⟩ := ih
      obtain ⟨c₂, hstep₂⟩ := exists_step_of_not_halted M (not_halted_of_chain M h hch)
      have hword := sstep_of_machine_step M hstep₂
      have heq := Step.det (machine_isLocal M) (weight_encCfg M c₁) hstep hword
      exact ⟨c₂, ReflTransGen.tail hch hstep₂, heq⟩

/-- **The simulation theorem.**  The machine halts from `c` if and only if the
word encoding `c` and the one-letter word `done` are equal in the monoid
presented by the rules of `M`.

Both directions are proved; nothing is assumed.  Together with
`machine_rules_finite` (the presentation is finite) this is the whole content
of the Markov--Post reduction, and all that separates it from the Markov--Post
theorem is a machine in this model with undecidable halting --- see
`SemigroupWordProblem.lean`. -/
theorem halts_iff_thueEquiv (M : Machine Γ Λ) (c : Cfg Γ Λ) :
    M.Halts c ↔
      ThueEquiv ruleSp rulePre rulePost (ruleRhs M) (encCfg M c) [Letter.done] := by
  constructor
  · intro h
    exact Derives.toThueEquiv (derives_done_of_halts M h)
  · intro h
    by_contra hnot
    have hder := (thueEquiv_iff_derives (machine_isLocal M) (weight_encCfg M c)
      (done_normalForm M)).1 h
    obtain ⟨c₁, -, hdone⟩ := orbit M hnot hder
    exact encCfg_ne_done M c₁ hdone.symm

/-- The presentation attached to a machine over a finite alphabet with finitely
many states is finite. -/
theorem machine_rules_finite [Finite Γ] [Finite Λ] (M : Machine Γ Λ) :
    {pq : List (Letter Γ Λ) × List (Letter Γ Λ) |
      Rules ruleSp rulePre rulePost (ruleRhs M) pq.1 pq.2}.Finite :=
  rules_finite ruleSp rulePre rulePost (ruleRhs M)

end Simulation

end SemigroupWordProblem
end GroupApproximation
