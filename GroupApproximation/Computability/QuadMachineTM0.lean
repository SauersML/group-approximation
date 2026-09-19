import GroupApproximation.Computability.QuadMachine
import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
# S9, part two: a two-stack machine simulates a Post--Turing machine

`Computability.QuadMachine` reads a modular machine as a machine on two stacks
of digits.  This file puts a Turing machine on those stacks.

The dictionary is forced by the shape of the step.  A `Turing.Tape` is a head
cell with a half-tape on each side; the two stacks are those two half-tapes,
with the head cell sitting on top of one of them --- `front`, the one being
scanned.  Which of the tape's two sides `front` is changes every time the head
turns around, because a step pushes onto exactly one stack.  A configuration
therefore carries that orientation, in its `side` bit and, redundantly, in its
state; the invariant `Rep` keeps the two in step.

Two points of care:

* **A `TM0` write does not move, and a two-stack step always does.**  A write
  is two steps: write the new symbol and step off the cell, then step back,
  writing back what was found.  The orientation flips twice, so it returns to
  what it was, and `Tape.move_left_right` says the tape does too.

* **Blanks are materialised, not stored.**  Reading past the end of a stack
  gives the digit `0`, which decodes to the blank; writing always writes a real
  symbol.  `Turing.ListBlank` identifies a stack with the same stack followed by
  blanks, which is exactly the slack this creates, so the invariant is stated
  with `ListBlank.mk` and nothing has to be trimmed.
-/

namespace GroupApproximation
namespace Computability

open Turing

/-- The data naming a Turing machine's alphabet and states by numbers.  Kept
abstract so the construction does not depend on how the finiteness of `Γ` and
`Λ` is witnessed. -/
structure TMData (Γ Λ : Type) [Inhabited Γ] where
  /-- The number of tape symbols. -/
  nsym : ℕ
  /-- The number of machine states. -/
  nstΛ : ℕ
  /-- A symbol's digit.  Never `0`: that digit means "past the end". -/
  encodeSym : Γ → ℕ
  /-- The symbol a digit names, with `0` naming the blank. -/
  decode : ℕ → Γ
  /-- A state's number. -/
  encodeSt : Λ → ℕ
  /-- The state a number names. -/
  decodeSt : ℕ → Λ
  /-- Decoding inverts encoding on symbols. -/
  decode_encodeSym : ∀ γ, decode (encodeSym γ) = γ
  /-- Symbols are not the end-of-stack digit. -/
  encodeSym_pos : ∀ γ, 1 ≤ encodeSym γ
  /-- Symbols are in range. -/
  encodeSym_le : ∀ γ, encodeSym γ ≤ nsym
  /-- The end-of-stack digit reads as a blank. -/
  decode_zero : decode 0 = default
  /-- Decoding inverts encoding on states. -/
  decodeSt_encodeSt : ∀ q, decodeSt (encodeSt q) = q
  /-- States are in range. -/
  encodeSt_lt : ∀ q, encodeSt q < nstΛ

/-- `true` for a rightward move. -/
def dirRight : Dir → Bool
  | Dir.right => true
  | Dir.left => false

namespace TMData

variable {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] (D : TMData Γ Λ)

/-- The number of a state, together with the two bits saying whether it is the
auxiliary state of a write and which way the head is facing. -/
def stIdx (q : Λ) (aux ori : Bool) : ℕ :=
  4 * D.encodeSt q + 2 * (if aux then 1 else 0) + (if ori then 1 else 0)

omit [Inhabited Λ] in
theorem stIdx_lt (q : Λ) (aux ori : Bool) : D.stIdx q aux ori < 4 * D.nstΛ := by
  have := D.encodeSt_lt q
  simp only [stIdx]
  rcases aux <;> rcases ori <;> simp <;> omega

omit [Inhabited Λ] in
theorem stIdx_div (q : Λ) (aux ori : Bool) : D.stIdx q aux ori / 4 = D.encodeSt q := by
  simp only [stIdx]
  rcases aux <;> rcases ori <;> simp <;> omega

omit [Inhabited Λ] in
theorem stIdx_aux (q : Λ) (aux ori : Bool) :
    (D.stIdx q aux ori / 2) % 2 = (if aux then 1 else 0) := by
  simp only [stIdx]
  rcases aux <;> rcases ori <;> simp <;> omega

omit [Inhabited Λ] in
theorem stIdx_ori (q : Λ) (aux ori : Bool) :
    D.stIdx q aux ori % 2 = (if ori then 1 else 0) := by
  simp only [stIdx]
  rcases aux <;> rcases ori <;> simp <;> omega

/-- Whether a state number is the auxiliary state of a write. -/
def auxOf (i : ℕ) : Bool := (i / 2) % 2 == 1

/-- Which way a state number says the head is facing. -/
def oriOf (i : ℕ) : Bool := i % 2 == 1

omit [Inhabited Λ] in
@[simp] theorem auxOf_stIdx (q : Λ) (aux ori : Bool) :
    auxOf (D.stIdx q aux ori) = aux := by
  simp only [auxOf, D.stIdx_aux]
  rcases aux <;> simp

omit [Inhabited Λ] in
@[simp] theorem oriOf_stIdx (q : Λ) (aux ori : Bool) :
    oriOf (D.stIdx q aux ori) = ori := by
  simp only [oriOf, D.stIdx_ori]
  rcases ori <;> simp

omit [Inhabited Λ] in
@[simp] theorem decodeSt_stIdx (q : Λ) (aux ori : Bool) :
    D.decodeSt (D.stIdx q aux ori / 4) = q := by
  rw [D.stIdx_div, D.decodeSt_encodeSt]

/-- The instruction table of the two-stack machine. -/
def δ (M : TM0.Machine Γ Λ) (i s : ℕ) : Option (ℕ × ℕ × Bool) :=
  if auxOf i then
    -- the second half of a write: step back, writing back what was found
    some (D.stIdx (D.decodeSt (i / 4)) false (!oriOf i), D.encodeSym (D.decode s), false)
  else
    match M (D.decodeSt (i / 4)) (D.decode s) with
    | none => none
    | some (q', TM0.Stmt.move d) =>
        some (D.stIdx q' false (dirRight d), D.encodeSym (D.decode s), dirRight d == oriOf i)
    | some (q', TM0.Stmt.write a) =>
        some (D.stIdx q' true (!oriOf i), D.encodeSym a, false)

theorem δ_aux (M : TM0.Machine Γ Λ) (q : Λ) (ori : Bool) (s : ℕ) :
    D.δ M (D.stIdx q true ori) s
      = some (D.stIdx q false (!ori), D.encodeSym (D.decode s), false) := by
  simp only [δ, D.auxOf_stIdx, D.oriOf_stIdx, D.decodeSt_stIdx, if_true]

theorem δ_normal (M : TM0.Machine Γ Λ) (q : Λ) (ori : Bool) (s : ℕ) :
    D.δ M (D.stIdx q false ori) s
      = (match M q (D.decode s) with
         | none => none
         | some (q', TM0.Stmt.move d) =>
             some (D.stIdx q' false (dirRight d), D.encodeSym (D.decode s),
               dirRight d == ori)
         | some (q', TM0.Stmt.write a) =>
             some (D.stIdx q' true (!ori), D.encodeSym a, false)) := by
  simp only [δ, D.auxOf_stIdx, D.oriOf_stIdx, D.decodeSt_stIdx, if_false,
    Bool.false_eq_true]

/-- **The two-stack machine of a Post--Turing machine.** -/
def toQuad (M : TM0.Machine Γ Λ) : QuadMachine where
  nsym := D.nsym
  nst := 4 * D.nstΛ
  δ := D.δ M
  δ_state_lt := by
    intro q s q' y mv h
    simp only [δ] at h
    split at h
    · rw [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact D.stIdx_lt _ _ _
    · split at h
      · exact absurd h (by simp)
      · rw [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]
        exact D.stIdx_lt _ _ _
      · rw [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]
        exact D.stIdx_lt _ _ _
  δ_write_pos := by
    intro q s q' y mv h
    simp only [δ] at h
    split at h
    · rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
      rw [← h.2.1]
      exact D.encodeSym_pos _
    · split at h
      · exact absurd h (by simp)
      · rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
        rw [← h.2.1]
        exact D.encodeSym_pos _
      · rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
        rw [← h.2.1]
        exact D.encodeSym_pos _
  δ_write_le := by
    intro q s q' y mv h
    simp only [δ] at h
    split at h
    · rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
      rw [← h.2.1]
      exact D.encodeSym_le _
    · split at h
      · exact absurd h (by simp)
      · rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
        rw [← h.2.1]
        exact D.encodeSym_le _
      · rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
        rw [← h.2.1]
        exact D.encodeSym_le _

@[simp] theorem toQuad_nsym (M : TM0.Machine Γ Λ) : (D.toQuad M).nsym = D.nsym := rfl

@[simp] theorem toQuad_nst (M : TM0.Machine Γ Λ) : (D.toQuad M).nst = 4 * D.nstΛ := rfl

@[simp] theorem toQuad_δ (M : TM0.Machine Γ Λ) : (D.toQuad M).δ = D.δ M := rfl

/-! ## The invariant -/

omit [Inhabited Λ] in
theorem headI_map (l : List ℕ) : (l.map D.decode).headI = D.decode l.headI := by
  cases l with
  | nil => simpa using D.decode_zero.symm
  | cons a l => simp

omit [Inhabited Λ] in
theorem tail_map (l : List ℕ) : (l.map D.decode).tail = l.tail.map D.decode := by
  cases l <;> simp

/-- **The tape a two-stack configuration represents.**  `side` says which of the
tape's two sides the scanned stack is; the head cell sits on top of it. -/
def RepTape (qc : QCfg) (T : Tape Γ) : Prop :=
  D.decode qc.front.headI = T.head ∧
    match qc.side with
    | true => ListBlank.mk (qc.front.tail.map D.decode) = T.right ∧
        ListBlank.mk (qc.back.map D.decode) = T.left
    | false => ListBlank.mk (qc.front.tail.map D.decode) = T.left ∧
        ListBlank.mk (qc.back.map D.decode) = T.right

omit [Inhabited Λ] in
/-- Stepping onto the stack being scanned. -/
theorem repTape_moveFront {back front : List ℕ} {st0 : ℕ} {side : Bool} {T : Tape Γ}
    (h : D.RepTape ⟨back, front, st0, side⟩ T) (y st : ℕ) :
    D.RepTape ⟨y :: back, front.tail, st, side⟩
      ((T.write (D.decode y)).move (if side then Dir.right else Dir.left)) := by
  obtain ⟨a, L, R⟩ := T
  cases side
  · obtain ⟨-, hf, hb⟩ := h
    have hf' : ListBlank.mk (front.tail.map D.decode) = L := hf
    have hb' : ListBlank.mk (back.map D.decode) = R := hb
    refine ⟨?_, ?_, ?_⟩
    · show D.decode front.tail.headI = L.head
      rw [← hf', ListBlank.head_mk, headI_map]
    · show ListBlank.mk (front.tail.tail.map D.decode) = L.tail
      rw [← hf', ListBlank.tail_mk, tail_map]
    · show ListBlank.mk (((y :: back).map D.decode)) = R.cons (D.decode y)
      rw [← hb', List.map_cons, ListBlank.cons_mk]
  · obtain ⟨-, hf, hb⟩ := h
    have hf' : ListBlank.mk (front.tail.map D.decode) = R := hf
    have hb' : ListBlank.mk (back.map D.decode) = L := hb
    refine ⟨?_, ?_, ?_⟩
    · show D.decode front.tail.headI = R.head
      rw [← hf', ListBlank.head_mk, headI_map]
    · show ListBlank.mk (front.tail.tail.map D.decode) = R.tail
      rw [← hf', ListBlank.tail_mk, tail_map]
    · show ListBlank.mk (((y :: back).map D.decode)) = L.cons (D.decode y)
      rw [← hb', List.map_cons, ListBlank.cons_mk]

omit [Inhabited Λ] in
/-- Stepping onto the other stack: the head turns around, and the orientation
flips with it. -/
theorem repTape_moveBack {back front : List ℕ} {st0 : ℕ} {side : Bool} {T : Tape Γ}
    (h : D.RepTape ⟨back, front, st0, side⟩ T) (y st : ℕ) :
    D.RepTape ⟨y :: front.tail, back, st, !side⟩
      ((T.write (D.decode y)).move (if side then Dir.left else Dir.right)) := by
  obtain ⟨a, L, R⟩ := T
  cases side
  · obtain ⟨-, hf, hb⟩ := h
    have hf' : ListBlank.mk (front.tail.map D.decode) = L := hf
    have hb' : ListBlank.mk (back.map D.decode) = R := hb
    refine ⟨?_, ?_, ?_⟩
    · show D.decode back.headI = R.head
      rw [← hb', ListBlank.head_mk, headI_map]
    · show ListBlank.mk (back.tail.map D.decode) = R.tail
      rw [← hb', ListBlank.tail_mk, tail_map]
    · show ListBlank.mk (((y :: front.tail).map D.decode)) = L.cons (D.decode y)
      rw [← hf', List.map_cons, ListBlank.cons_mk]
  · obtain ⟨-, hf, hb⟩ := h
    have hf' : ListBlank.mk (front.tail.map D.decode) = R := hf
    have hb' : ListBlank.mk (back.map D.decode) = L := hb
    refine ⟨?_, ?_, ?_⟩
    · show D.decode back.headI = L.head
      rw [← hb', ListBlank.head_mk, headI_map]
    · show ListBlank.mk (back.tail.map D.decode) = L.tail
      rw [← hb', ListBlank.tail_mk, tail_map]
    · show ListBlank.mk (((y :: front.tail).map D.decode)) = R.cons (D.decode y)
      rw [← hf', List.map_cons, ListBlank.cons_mk]

/-- The two-stack configuration represents the Post--Turing configuration. -/
structure Rep (M : TM0.Machine Γ Λ) (qc : QCfg) (X : TM0.Cfg Γ Λ) : Prop where
  /-- Digits are symbols. -/
  wf : (D.toQuad M).WF qc
  /-- The state, with the orientation the `side` bit records. -/
  state : qc.state = D.stIdx X.q false qc.side
  /-- The tape. -/
  tape : D.RepTape qc X.Tape

/-- The same, midway through a write. -/
structure RepAux (M : TM0.Machine Γ Λ) (qc : QCfg) (q : Λ) (T : Tape Γ) : Prop where
  /-- Digits are symbols. -/
  wf : (D.toQuad M).WF qc
  /-- The auxiliary state. -/
  state : qc.state = D.stIdx q true qc.side
  /-- The tape. -/
  tape : D.RepTape qc T

omit [Inhabited Λ] in
theorem dir_of_eq {d : Dir} {side : Bool} (h : dirRight d = side) :
    (if side then Dir.right else Dir.left) = d := by
  cases d <;> cases side <;> simp_all [dirRight]

omit [Inhabited Λ] in
theorem dir_of_ne {d : Dir} {side : Bool} (h : dirRight d = !side) :
    (if side then Dir.left else Dir.right) = d := by
  cases d <;> cases side <;> simp_all [dirRight]

theorem qsteps_one {Q : QuadMachine} {qc qc' : QCfg} (h : Q.qstep qc = some qc') :
    Q.qsteps 1 qc = some qc' := by
  rw [QuadMachine.qsteps_succ, h]
  rfl

theorem qsteps_two {Q : QuadMachine} {qc qc₁ qc₂ : QCfg} (h1 : Q.qstep qc = some qc₁)
    (h2 : Q.qstep qc₁ = some qc₂) : Q.qsteps 2 qc = some qc₂ := by
  rw [QuadMachine.qsteps_succ, h1]
  exact qsteps_one h2

theorem qsteps_add {Q : QuadMachine} : ∀ (k n : ℕ) {qc qc' qc'' : QCfg},
    Q.qsteps k qc = some qc' → Q.qsteps n qc' = some qc'' → Q.qsteps (k + n) qc = some qc''
  | 0, n, qc, qc', qc'', h1, h2 => by
      obtain rfl : qc = qc' := Option.some.inj h1
      simpa using h2
  | k + 1, n, qc, qc', qc'', h1, h2 => by
      rw [QuadMachine.qsteps_succ] at h1
      rcases hq : Q.qstep qc with _ | qc₁
      · rw [hq] at h1; exact absurd h1 (by simp)
      · rw [hq] at h1
        have h1' : Q.qsteps k qc₁ = some qc' := h1
        show Q.qsteps (k + 1 + n) qc = some qc''
        rw [show k + 1 + n = (k + n) + 1 by ring, QuadMachine.qsteps_succ, hq]
        exact qsteps_add k n h1' h2

/-! ## The simulation

A `move` is one two-stack step; a `write` is two.  In both cases the written
digit is a real symbol, so the invariant's digit conditions survive, and the
orientation ends where the state says it should. -/

omit [Inhabited Λ] in
theorem decode_eq_of_beq_false {d : Dir} {side : Bool} (h : (dirRight d == side) = false) :
    dirRight d = !side := by
  cases d <;> cases side <;> simp_all [dirRight]

omit [Inhabited Λ] in
theorem decode_eq_of_beq_true {d : Dir} {side : Bool} (h : (dirRight d == side) = true) :
    dirRight d = side := by
  cases d <;> cases side <;> simp_all [dirRight]

/-- **A `move` is one step.** -/
theorem step_sim_move {M : TM0.Machine Γ Λ} {back front : List ℕ} {st0 : ℕ} {side : Bool}
    {X_q q' : Λ} {T : Tape Γ} {d : Dir}
    (hwf : (D.toQuad M).WF ⟨back, front, st0, side⟩)
    (hst : st0 = D.stIdx X_q false side)
    (htape : D.RepTape ⟨back, front, st0, side⟩ T)
    (hM : M X_q T.head = some (q', TM0.Stmt.move d)) :
    ∃ qc', (D.toQuad M).qstep ⟨back, front, st0, side⟩ = some qc' ∧
      D.Rep M qc' ⟨q', T.move d⟩ := by
  have hhead : D.decode front.headI = T.head := htape.1
  have hδ : (D.toQuad M).δ st0 front.headI
      = some (D.stIdx q' false (dirRight d), D.encodeSym T.head, dirRight d == side) := by
    rw [hst]
    show D.δ M (D.stIdx X_q false side) front.headI = _
    rw [D.δ_normal, hhead, hM]
  have hdec : D.decode (D.encodeSym T.head) = T.head := D.decode_encodeSym _
  cases hmv : (dirRight d == side)
  · have hdir : dirRight d = !side := decode_eq_of_beq_false hmv
    refine ⟨⟨D.encodeSym T.head :: front.tail, back,
      D.stIdx q' false (dirRight d), !side⟩, ?_, ?_⟩
    · show ((D.toQuad M).δ st0 front.headI).map _ = _
      rw [hδ, hmv]
      rfl
    · refine ⟨?_, ?_, ?_⟩
      · exact hwf.qstep (by
          show ((D.toQuad M).δ st0 front.headI).map _ = _
          rw [hδ, hmv]
          rfl)
      · show D.stIdx q' false (dirRight d) = D.stIdx q' false (!side)
        rw [hdir]
      · have := D.repTape_moveBack htape (D.encodeSym T.head)
          (D.stIdx q' false (dirRight d))
        rwa [hdec, Tape.write_self, dir_of_ne hdir] at this
  · have hdir : dirRight d = side := decode_eq_of_beq_true hmv
    refine ⟨⟨D.encodeSym T.head :: back, front.tail,
      D.stIdx q' false (dirRight d), side⟩, ?_, ?_⟩
    · show ((D.toQuad M).δ st0 front.headI).map _ = _
      rw [hδ, hmv]
      rfl
    · refine ⟨?_, ?_, ?_⟩
      · exact hwf.qstep (by
          show ((D.toQuad M).δ st0 front.headI).map _ = _
          rw [hδ, hmv]
          rfl)
      · show D.stIdx q' false (dirRight d) = D.stIdx q' false side
        rw [hdir]
      · have := D.repTape_moveFront htape (D.encodeSym T.head)
          (D.stIdx q' false (dirRight d))
        rwa [hdec, Tape.write_self, dir_of_eq hdir] at this

/-- **A `write` is two steps**: off the cell and back, and the tape returns with
`Tape.move_left_right`. -/
theorem step_sim_write {M : TM0.Machine Γ Λ} {back front : List ℕ} {st0 : ℕ} {side : Bool}
    {X_q q' : Λ} {T : Tape Γ} {b : Γ}
    (hwf : (D.toQuad M).WF ⟨back, front, st0, side⟩)
    (hst : st0 = D.stIdx X_q false side)
    (htape : D.RepTape ⟨back, front, st0, side⟩ T)
    (hM : M X_q T.head = some (q', TM0.Stmt.write b)) :
    ∃ qc₁ qc₂, (D.toQuad M).qstep ⟨back, front, st0, side⟩ = some qc₁ ∧
      (D.toQuad M).qstep qc₁ = some qc₂ ∧ D.Rep M qc₂ ⟨q', T.write b⟩ := by
  have hhead : D.decode front.headI = T.head := htape.1
  have hδ : (D.toQuad M).δ st0 front.headI
      = some (D.stIdx q' true (!side), D.encodeSym b, false) := by
    rw [hst]
    show D.δ M (D.stIdx X_q false side) front.headI = _
    rw [D.δ_normal, hhead, hM]
  set qc₁ : QCfg := ⟨D.encodeSym b :: front.tail, back, D.stIdx q' true (!side), !side⟩
    with hqc₁
  have hstep₁ : (D.toQuad M).qstep ⟨back, front, st0, side⟩ = some qc₁ := by
    show ((D.toQuad M).δ st0 front.headI).map _ = _
    rw [hδ]
    rfl
  have hwf₁ : (D.toQuad M).WF qc₁ := hwf.qstep hstep₁
  -- the tape after the first step
  set T₁ : Tape Γ := (T.write b).move (if side then Dir.left else Dir.right) with hT₁
  have htape₁ : D.RepTape qc₁ T₁ := by
    have := D.repTape_moveBack htape (D.encodeSym b) (D.stIdx q' true (!side))
    rwa [D.decode_encodeSym] at this
  have hhead₁ : D.decode qc₁.front.headI = T₁.head := htape₁.1
  have hδ₁ : (D.toQuad M).δ qc₁.state qc₁.front.headI
      = some (D.stIdx q' false side, D.encodeSym T₁.head, false) := by
    show D.δ M (D.stIdx q' true (!side)) qc₁.front.headI = _
    rw [D.δ_aux, hhead₁, Bool.not_not]
  refine ⟨qc₁, ⟨D.encodeSym T₁.head :: qc₁.front.tail, qc₁.back,
    D.stIdx q' false side, !qc₁.side⟩, hstep₁, ?_, ?_⟩
  · show ((D.toQuad M).δ qc₁.state qc₁.front.headI).map _ = _
    rw [hδ₁]
    rfl
  · refine ⟨?_, ?_, ?_⟩
    · exact hwf₁.qstep (by
        show ((D.toQuad M).δ qc₁.state qc₁.front.headI).map _ = _
        rw [hδ₁]
        rfl)
    · show D.stIdx q' false side = D.stIdx q' false (!qc₁.side)
      rw [hqc₁, Bool.not_not]
    · have := D.repTape_moveBack htape₁ (D.encodeSym T₁.head) (D.stIdx q' false side)
      rw [D.decode_encodeSym, Tape.write_self] at this
      have hmove : T₁.move (if qc₁.side then Dir.left else Dir.right) = T.write b := by
        rw [hqc₁, hT₁]
        cases side <;> simp
      rwa [hmove] at this

/-! ## Halting agrees -/

/-- The Post--Turing machine halts: it reaches a configuration with no next
step. -/
def TMHalts (M : TM0.Machine Γ Λ) (X : TM0.Cfg Γ Λ) : Prop :=
  ∃ X', TM0.Reaches M X X' ∧ TM0.step M X' = none

theorem TMHalts.head {M : TM0.Machine Γ Λ} {X X' : TM0.Cfg Γ Λ}
    (hstep : TM0.step M X = some X') (h : TMHalts M X') : TMHalts M X := by
  obtain ⟨X'', hreach, hnone⟩ := h
  exact ⟨X'', Relation.ReflTransGen.head hstep hreach, hnone⟩

theorem qstep_eq_none_iff {M : TM0.Machine Γ Λ} {qc : QCfg} {X : TM0.Cfg Γ Λ}
    (h : D.Rep M qc X) : (D.toQuad M).qstep qc = none ↔ TM0.step M X = none := by
  obtain ⟨back, front, st0, side⟩ := qc
  obtain ⟨X_q, T⟩ := X
  have hhead : D.decode front.headI = T.head := h.tape.1
  have hst : st0 = D.stIdx X_q false side := h.state
  have hδ : (D.toQuad M).δ st0 front.headI
      = (match M X_q T.head with
         | none => none
         | some (q', TM0.Stmt.move d) =>
             some (D.stIdx q' false (dirRight d), D.encodeSym T.head, dirRight d == side)
         | some (q', TM0.Stmt.write a) =>
             some (D.stIdx q' true (!side), D.encodeSym a, false)) := by
    rw [hst]
    show D.δ M (D.stIdx X_q false side) front.headI = _
    rw [D.δ_normal, hhead]
  have h1 : (D.toQuad M).qstep ⟨back, front, st0, side⟩ = none
      ↔ (D.toQuad M).δ st0 front.headI = none := by
    simp [QuadMachine.qstep]
  have h2 : TM0.step M (⟨X_q, T⟩ : TM0.Cfg Γ Λ) = none ↔ M X_q T.head = none := by
    simp [TM0.step]
  rw [h1, h2, hδ]
  cases hM : M X_q T.head with
  | none => simp
  | some p => obtain ⟨q', a⟩ := p; cases a <;> simp

/-- One machine step is one or two two-stack steps. -/
theorem step_sim_or {M : TM0.Machine Γ Λ} {qc : QCfg} {X X' : TM0.Cfg Γ Λ}
    (h : D.Rep M qc X) (hstep : TM0.step M X = some X') :
    (∃ qcA, (D.toQuad M).qstep qc = some qcA ∧ D.Rep M qcA X') ∨
      (∃ qc₁ qc₂, (D.toQuad M).qstep qc = some qc₁ ∧ (D.toQuad M).qstep qc₁ = some qc₂ ∧
        D.Rep M qc₂ X') := by
  obtain ⟨back, front, st0, side⟩ := qc
  obtain ⟨X_q, T⟩ := X
  have hwf := h.wf
  have hst := h.state
  have htape := h.tape
  have hstep' : (M X_q T.head).map
      (fun p => (⟨p.1, match p.2 with
        | TM0.Stmt.move d => T.move d
        | TM0.Stmt.write a => T.write a⟩ : TM0.Cfg Γ Λ)) = some X' := hstep
  cases hM : M X_q T.head with
  | none => rw [hM] at hstep'; exact absurd hstep' (by simp)
  | some p =>
      obtain ⟨q', a⟩ := p
      rw [hM] at hstep'
      cases a with
      | move d =>
          have hX' : X' = (⟨q', T.move d⟩ : TM0.Cfg Γ Λ) := (Option.some.inj hstep').symm
          obtain ⟨qcA, hq, hrep⟩ := D.step_sim_move hwf hst htape hM
          exact Or.inl ⟨qcA, hq, by rw [hX']; exact hrep⟩
      | write b =>
          have hX' : X' = (⟨q', T.write b⟩ : TM0.Cfg Γ Λ) := (Option.some.inj hstep').symm
          obtain ⟨qc₁, qc₂, hq1, hq2, hrep⟩ := D.step_sim_write hwf hst htape hM
          exact Or.inr ⟨qc₁, qc₂, hq1, hq2, by rw [hX']; exact hrep⟩

/-- **The machine halts, so the two-stack machine does.** -/
theorem QHalts_of_reaches {M : TM0.Machine Γ Λ} {X X' : TM0.Cfg Γ Λ}
    (hreach : TM0.Reaches M X X') (hnone : TM0.step M X' = none) :
    ∀ qc, D.Rep M qc X → (D.toQuad M).QHalts qc := by
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun qc h => ⟨0, qc, rfl, (D.qstep_eq_none_iff h).2 hnone⟩
  | @head X₁ X₂ hstep _ ih =>
      intro qc h
      have hstep' : TM0.step M X₁ = some X₂ := hstep
      rcases D.step_sim_or h hstep' with ⟨qcA, hq, hrep⟩ | ⟨qc₁, qc₂, hq1, hq2, hrep⟩
      · obtain ⟨n, qc'', hn, hnone'⟩ := ih qcA hrep
        exact ⟨1 + n, qc'', qsteps_add 1 n (qsteps_one hq) hn, hnone'⟩
      · obtain ⟨n, qc'', hn, hnone'⟩ := ih qc₂ hrep
        exact ⟨2 + n, qc'', qsteps_add 2 n (qsteps_two hq1 hq2) hn, hnone'⟩

/-- **The two-stack machine halts, so the machine does.** -/
theorem TMHalts_of_qsteps {M : TM0.Machine Γ Λ} (k : ℕ) :
    ∀ {qc qc' : QCfg} {X : TM0.Cfg Γ Λ}, D.Rep M qc X →
      (D.toQuad M).qsteps k qc = some qc' → (D.toQuad M).qstep qc' = none →
      TMHalts M X := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro qc qc' X h hk hnone
    rcases hq : (D.toQuad M).qstep qc with _ | qc₁
    · exact ⟨X, Relation.ReflTransGen.refl, (D.qstep_eq_none_iff h).1 hq⟩
    · rcases hX : TM0.step M X with _ | X'
      · rw [(D.qstep_eq_none_iff h).2 hX] at hq
        exact absurd hq (by simp)
      · rcases D.step_sim_or h hX with ⟨qcA, hqA, hrepA⟩ | ⟨qcB₁, qcB₂, hb1, hb2, hrepB⟩
        · cases k with
          | zero =>
              obtain rfl : qc = qc' := Option.some.inj hk
              rw [hq] at hnone
              exact absurd hnone (by simp)
          | succ m =>
              rw [QuadMachine.qsteps_succ, hqA] at hk
              have hk' : (D.toQuad M).qsteps m qcA = some qc' := hk
              exact TMHalts.head hX (ih m (by omega) hrepA hk' hnone)
        · cases k with
          | zero =>
              obtain rfl : qc = qc' := Option.some.inj hk
              rw [hq] at hnone
              exact absurd hnone (by simp)
          | succ m =>
              cases m with
              | zero =>
                  rw [QuadMachine.qsteps_succ, hb1] at hk
                  have hk' : (D.toQuad M).qsteps 0 qcB₁ = some qc' := hk
                  obtain rfl : qcB₁ = qc' := Option.some.inj hk'
                  rw [hb2] at hnone
                  exact absurd hnone (by simp)
              | succ m' =>
                  rw [QuadMachine.qsteps_succ, hb1] at hk
                  have hk1 : (D.toQuad M).qsteps (m' + 1) qcB₁ = some qc' := hk
                  rw [QuadMachine.qsteps_succ, hb2] at hk1
                  have hk' : (D.toQuad M).qsteps m' qcB₂ = some qc' := hk1
                  exact TMHalts.head hX (ih m' (by omega) hrepB hk' hnone)

/-- **S9's simulation.**  The two-stack machine halts from an encoded
configuration exactly when the Post--Turing machine halts. -/
theorem QHalts_iff_TMHalts {M : TM0.Machine Γ Λ} {qc : QCfg} {X : TM0.Cfg Γ Λ}
    (h : D.Rep M qc X) : (D.toQuad M).QHalts qc ↔ TMHalts M X := by
  constructor
  · rintro ⟨k, qc', hk, hnone⟩
    exact D.TMHalts_of_qsteps k h hk hnone
  · rintro ⟨X', hreach, hnone⟩
    exact D.QHalts_of_reaches hreach hnone qc h

end TMData
end Computability
end GroupApproximation
