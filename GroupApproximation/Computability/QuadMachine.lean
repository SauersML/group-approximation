import GroupApproximation.Computability.BooneGroupModularMachine

/-!
# S9, part one: a modular machine is a two-stack machine

Simpson leaves one thing to the reader: that some modular machine has a
non-computable halting set (his Theorem 4).  This file supplies the machine
half of that, and it is the only place where the shape of a modular machine's
step is taken seriously.

Read a configuration `(α, β)` in base `m`.  A step pops the last digit of each
of `α` and `β` and pushes two digits onto one of them, so `α` and `β` are two
stacks and a step moves one cell from one to the other: a modular machine *is*
a Turing machine whose tape has been cut at the head.

That reading is what this file formalises.  A `QuadMachine` is a machine on two
stacks of digits, `back` (which carries the state on top) and `front` (whose top
is the scanned cell); `encCfg` reads a configuration as a pair of naturals, and
`step_encCfg` says that one machine step is one modular-machine step.

Two points where the design is forced:

* **Orientation.**  A step pushes onto exactly one stack, so the state cannot
  stay on the same side while the head turns around.  A configuration therefore
  carries a `side` bit saying which of `α`, `β` holds the state, and a move
  *toward the back* flips it.  The quadruple table never sees `side`: the
  digits are tagged, and the tag of the state a quadruple pushes is determined
  by the quadruple's own direction, which is exactly the bookkeeping the two
  formats need.

* **Digit `0` is not a symbol.**  A modular machine halts by *reaching* `(0,0)`,
  so a halting computation must erase both stacks, and erasing needs to know
  when a stack is empty.  A stack is empty exactly when its digit is `0`, so
  `0` must never occur inside one: tape symbols are the digits `1 … nsym`, and
  `0` means "past the end", materialising a blank when read.

With that, erasure is four quadruples and no end markers: transfer `α` onto `β`
one digit at a time, and when `α` runs out (its digit reads `0`) drain `β` the
same way, ending at `(0,0)` when its digit reads `0` too.
-/

namespace GroupApproximation
namespace Computability

open GroupApproximation.BooneGroup (ModularMachine)

/-- **A two-stack machine.**  `δ q s` is the instruction for state `q` scanning
digit `s` (with `s = 0` meaning "past the end of the stack", read as a blank);
it writes `y`, moves, and changes state.  The Boolean says whether the head
moves *toward the front* --- the stack it was scanning --- or turns around. -/
structure QuadMachine where
  /-- The number of tape symbols.  They are the digits `1 … nsym`. -/
  nsym : ℕ
  /-- The number of machine states. -/
  nst : ℕ
  /-- The instruction table. -/
  δ : ℕ → ℕ → Option (ℕ × ℕ × Bool)
  /-- Instructions land in the state set. -/
  δ_state_lt : ∀ {q s q' y : ℕ} {mv : Bool}, δ q s = some (q', y, mv) → q' < nst
  /-- The written symbol is a symbol: never the end-of-stack digit `0`. -/
  δ_write_pos : ∀ {q s q' y : ℕ} {mv : Bool}, δ q s = some (q', y, mv) → 1 ≤ y
  /-- The written symbol is in range. -/
  δ_write_le : ∀ {q s q' y : ℕ} {mv : Bool}, δ q s = some (q', y, mv) → y ≤ nsym

namespace QuadMachine

variable (Q : QuadMachine)

/-! ## Digits

Two cleanup states are added to the machine's own: `e1` transfers `α` onto `β`,
`e2` drains `β`.  Each state occurs as two digits, one for each orientation. -/

/-- The number of states of the modular machine: the machine's own, plus the
two cleanup states. -/
def nstAll : ℕ := Q.nst + 2

/-- The transfer state. -/
def e1 : ℕ := Q.nst

/-- The drain state. -/
def e2 : ℕ := Q.nst + 1

/-- The modulus.  Digits: `0` for "past the end", `1 … nsym` for symbols, then
one block of state digits for each orientation. -/
def m : ℕ := Q.nsym + 2 * Q.nstAll + 1

/-- The digit of state `q` when the state sits on the `α` side. -/
def tagA (q : ℕ) : ℕ := Q.nsym + 1 + q

/-- The digit of state `q` when the state sits on the `β` side. -/
def tagB (q : ℕ) : ℕ := Q.nsym + Q.nstAll + 1 + q

theorem one_lt_m : 1 < Q.m := by
  have : 0 < Q.nstAll := by simp only [nstAll]; omega
  simp only [m]
  omega

theorem m_pos : 0 < Q.m := lt_trans Nat.zero_lt_one Q.one_lt_m

theorem tagA_lt {q : ℕ} (h : q < Q.nstAll) : Q.tagA q < Q.m := by
  simp only [tagA, m]
  omega

theorem tagB_lt {q : ℕ} (h : q < Q.nstAll) : Q.tagB q < Q.m := by
  simp only [tagB, m]
  omega

theorem e1_lt : Q.e1 < Q.nstAll := by simp only [e1, nstAll]; omega

theorem e2_lt : Q.e2 < Q.nstAll := by simp only [e2, nstAll]; omega

theorem tagA_pos (q : ℕ) : 0 < Q.tagA q := by simp only [tagA]; omega

theorem tagB_pos (q : ℕ) : 0 < Q.tagB q := by simp only [tagB, nstAll]; omega

theorem nsym_lt_tagA (q : ℕ) : Q.nsym < Q.tagA q := by simp only [tagA]; omega

theorem tagA_lt_tagB (q q' : ℕ) (h : q < Q.nstAll) : Q.tagA q < Q.tagB q' := by
  simp only [tagA, tagB]
  omega

theorem tagA_injective {q q' : ℕ} (h : Q.tagA q = Q.tagA q') : q = q' := by
  simp only [tagA] at h; omega

theorem tagB_injective {q q' : ℕ} (h : Q.tagB q = Q.tagB q') : q = q' := by
  simp only [tagB] at h; omega

/-! ## The quadruple table

Five cases, tried in order.  The first two are the cleanup; the next two are the
simulation, in each of the two orientations; anything else has no quadruple.
The simulation cases require the *other* digit to be a symbol, so they cannot
collide with each other, and the cleanup cases are tried first, so the whole
table is a function by construction. -/

/-- The state a machine-state digit on the `α` side denotes, if any. -/
def isSimA (a : ℕ) : Prop := Q.nsym + 1 ≤ a ∧ a ≤ Q.nsym + Q.nst

/-- The state a machine-state digit on the `β` side denotes, if any. -/
def isSimB (b : ℕ) : Prop := Q.nsym + Q.nstAll + 1 ≤ b ∧ b ≤ Q.nsym + Q.nstAll + Q.nst

instance (a : ℕ) : Decidable (Q.isSimA a) := by unfold isSimA; infer_instance
instance (b : ℕ) : Decidable (Q.isSimB b) := by unfold isSimB; infer_instance

/-- The instruction a simulation state emits, in the orientation whose stable
digit is `tagA`. -/
def simEmit (q' y : ℕ) (mv : Bool) (sideA : Bool) : ℕ × Bool :=
  -- moving toward the front keeps the orientation; turning around flips it
  if (mv == sideA) then (y * Q.m + Q.tagA q', true) else (y * Q.m + Q.tagB q', false)

/-- **The table.** -/
def quadOf (a b : ℕ) : Option (ℕ × Bool) :=
  if a = 0 ∧ b = 0 then none
  else if a < Q.m ∧ b < Q.m then
    if a = Q.tagA Q.e2 then
      (if b = 0 then some (0, true) else some (Q.tagA Q.e2, true))
    else if b = Q.tagB Q.e1 then
      (if a = 0 then some (Q.tagA Q.e2, true)
       else some (a * Q.m + Q.tagB Q.e1, false))
    else if Q.isSimA a ∧ b ≤ Q.nsym then
      (match Q.δ (a - (Q.nsym + 1)) b with
       | some (q', y, mv) => some (Q.simEmit q' y mv true)
       | none => some (Q.m + Q.tagB Q.e1, false))
    else if Q.isSimB b ∧ a ≤ Q.nsym then
      (match Q.δ (b - (Q.nsym + Q.nstAll + 1)) a with
       | some (q', y, mv) => some (Q.simEmit q' y mv false)
       | none => some (Q.m + Q.tagB Q.e1, false))
    else none
  else none

theorem quadOf_eq_none_of_le_left {a b : ℕ} (h : Q.m ≤ a) : Q.quadOf a b = none := by
  unfold quadOf
  have hpos := Q.m_pos
  rw [if_neg (by omega : ¬(a = 0 ∧ b = 0)), if_neg (by omega : ¬(a < Q.m ∧ b < Q.m))]

theorem quadOf_eq_none_of_le_right {a b : ℕ} (h : Q.m ≤ b) : Q.quadOf a b = none := by
  unfold quadOf
  have hpos := Q.m_pos
  rw [if_neg (by omega : ¬(a = 0 ∧ b = 0)), if_neg (by omega : ¬(a < Q.m ∧ b < Q.m))]

theorem quadOf_zero_zero : Q.quadOf 0 0 = none := by
  simp [quadOf]

theorem simEmit_lt {q' y : ℕ} (hq : q' < Q.nstAll) (hy : y < Q.m) (mv sideA : Bool) :
    (Q.simEmit q' y mv sideA).1 < Q.m ^ 2 := by
  have hA := Q.tagA_lt hq
  have hB := Q.tagB_lt hq
  simp only [simEmit]
  split
  · have : y * Q.m + Q.tagA q' < Q.m * Q.m := by
      calc y * Q.m + Q.tagA q' < y * Q.m + Q.m := by omega
        _ = (y + 1) * Q.m := by ring
        _ ≤ Q.m * Q.m := Nat.mul_le_mul_right _ (by omega)
    simpa [pow_two] using this
  · have : y * Q.m + Q.tagB q' < Q.m * Q.m := by
      calc y * Q.m + Q.tagB q' < y * Q.m + Q.m := by omega
        _ = (y + 1) * Q.m := by ring
        _ ≤ Q.m * Q.m := Nat.mul_le_mul_right _ (by omega)
    simpa [pow_two] using this

theorem quadOf_lt {a b c : ℕ} {d : Bool} (h : Q.quadOf a b = some (c, d)) :
    c < Q.m ^ 2 := by
  have hmm : Q.m ≤ Q.m ^ 2 := by
    have := Q.one_lt_m
    calc Q.m = Q.m * 1 := (mul_one _).symm
      _ ≤ Q.m * Q.m := Nat.mul_le_mul_left _ (by omega)
      _ = Q.m ^ 2 := (pow_two _).symm
  have hB1 := Q.tagB_lt Q.e1_lt
  have hA2 := Q.tagA_lt Q.e2_lt
  simp only [quadOf] at h
  split at h
  · exact absurd h (by simp)
  split at h
  · rename_i hab
    split at h
    · split at h <;> (rw [Option.some.injEq, Prod.mk.injEq] at h; omega)
    · split at h
      · split at h
        · rw [Option.some.injEq, Prod.mk.injEq] at h; omega
        · rw [Option.some.injEq, Prod.mk.injEq] at h
          have : a * Q.m + Q.tagB Q.e1 < Q.m * Q.m := by
            calc a * Q.m + Q.tagB Q.e1 < a * Q.m + Q.m := by omega
              _ = (a + 1) * Q.m := by ring
              _ ≤ Q.m * Q.m := Nat.mul_le_mul_right _ (by omega)
          rw [pow_two]
          omega
      · split at h
        · rename_i hsim
          split at h
          · rename_i q' y mv hδ
            rw [Option.some.injEq, Prod.mk.injEq] at h
            have hy := Q.δ_write_le hδ
            have hq := Q.δ_state_lt hδ
            have := Q.simEmit_lt (q' := q') (y := y)
              (by simp only [nstAll]; omega) (by simp only [m]; omega) mv true
            omega
          · rw [Option.some.injEq, Prod.mk.injEq] at h
            have : Q.m + Q.tagB Q.e1 < Q.m * Q.m := by
              calc Q.m + Q.tagB Q.e1 < Q.m + Q.m := by omega
                _ = 2 * Q.m := by ring
                _ ≤ Q.m * Q.m := Nat.mul_le_mul_right _ (by omega)
            rw [pow_two]; omega
        · split at h
          · rename_i hsim
            split at h
            · rename_i q' y mv hδ
              rw [Option.some.injEq, Prod.mk.injEq] at h
              have hy := Q.δ_write_le hδ
              have hq := Q.δ_state_lt hδ
              have := Q.simEmit_lt (q' := q') (y := y)
                (by simp only [nstAll]; omega) (by simp only [m]; omega) mv false
              omega
            · rw [Option.some.injEq, Prod.mk.injEq] at h
              have : Q.m + Q.tagB Q.e1 < Q.m * Q.m := by
                calc Q.m + Q.tagB Q.e1 < Q.m + Q.m := by omega
                  _ = 2 * Q.m := by ring
                  _ ≤ Q.m * Q.m := Nat.mul_le_mul_right _ (by omega)
              rw [pow_two]; omega
          · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **The modular machine a two-stack machine induces.** -/
def toModular : ModularMachine where
  size := Q.m
  one_lt_size := Q.one_lt_m
  quad := Q.quadOf
  quad_eq_none_left := Q.quadOf_eq_none_of_le_left
  quad_eq_none_right := Q.quadOf_eq_none_of_le_right
  quad_lt := Q.quadOf_lt
  quad_zero_zero := Q.quadOf_zero_zero

@[simp] theorem toModular_size : Q.toModular.size = Q.m := rfl

@[simp] theorem toModular_quad (a b : ℕ) : Q.toModular.quad a b = Q.quadOf a b := rfl

/-! ## Reading a configuration as a pair of naturals -/

end QuadMachine

/-- Base-`m` digits, least significant first. -/
def encList (m : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: l => d + m * encList m l

@[simp] theorem encList_nil (m : ℕ) : encList m [] = 0 := rfl

@[simp] theorem encList_cons (m d : ℕ) (l : List ℕ) :
    encList m (d :: l) = d + m * encList m l := rfl

theorem encList_mod {m : ℕ} :
    ∀ {l : List ℕ}, (∀ d ∈ l, d < m) → encList m l % m = l.headI
  | [], _ => by simp [Nat.zero_mod]
  | d :: l, h => by
      have hd : d < m := h d (List.mem_cons_self ..)
      simp only [encList_cons, List.headI_cons, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hd

theorem encList_div {m : ℕ} (hm : 0 < m) :
    ∀ {l : List ℕ}, (∀ d ∈ l, d < m) → encList m l / m = encList m l.tail
  | [], _ => by simp [Nat.zero_div]
  | d :: l, h => by
      have hd : d < m := h d (List.mem_cons_self ..)
      simp only [encList_cons, List.tail_cons, Nat.add_mul_div_left _ _ hm,
        Nat.div_eq_of_lt hd, Nat.zero_add]

/-- A configuration of a two-stack machine: the stack carrying the state, the
stack being scanned, the state, and which of `α`, `β` carries the state. -/
structure QCfg where
  /-- The stack whose top is the state digit. -/
  back : List ℕ
  /-- The stack whose top is the scanned cell. -/
  front : List ℕ
  /-- The state. -/
  state : ℕ
  /-- `true` when the state sits on the `α` side. -/
  side : Bool

namespace QuadMachine

variable (Q : QuadMachine)

/-- **The configuration, read as a pair of naturals.** -/
def encCfg (c : QCfg) : ℕ × ℕ :=
  if c.side then
    (Q.tagA c.state + Q.m * encList Q.m c.back, encList Q.m c.front)
  else
    (encList Q.m c.front, Q.tagB c.state + Q.m * encList Q.m c.back)

/-- The configuration is one the simulation can be in: both stacks hold
symbols, and the state is one of the machine's own. -/
structure WF (c : QCfg) : Prop where
  /-- The back stack holds symbols. -/
  back_mem : ∀ d ∈ c.back, 1 ≤ d ∧ d ≤ Q.nsym
  /-- The front stack holds symbols. -/
  front_mem : ∀ d ∈ c.front, 1 ≤ d ∧ d ≤ Q.nsym
  /-- The state is one of the machine's own. -/
  state_lt : c.state < Q.nst

theorem lt_m_of_le_nsym {d : ℕ} (h : d ≤ Q.nsym) : d < Q.m := by
  simp only [m, nstAll]; omega

theorem WF.digits_lt {Q : QuadMachine} {c : QCfg} (hc : Q.WF c) :
    (∀ d ∈ c.back, d < Q.m) ∧ (∀ d ∈ c.front, d < Q.m) :=
  ⟨fun d hd => Q.lt_m_of_le_nsym (hc.back_mem d hd).2,
    fun d hd => Q.lt_m_of_le_nsym (hc.front_mem d hd).2⟩

/-- **One machine step.**  The written symbol is pushed onto the stack that will
carry the state; the scanned cell is popped.  Moving toward the back turns the
head around, which is what swaps the roles of the two stacks. -/
def qstep (c : QCfg) : Option QCfg :=
  (Q.δ c.state c.front.headI).map fun r =>
    match r.2.2 with
    | true => ⟨r.2.1 :: c.back, c.front.tail, r.1, c.side⟩
    | false => ⟨r.2.1 :: c.front.tail, c.back, r.1, !c.side⟩

theorem WF.qstep {Q : QuadMachine} {c c' : QCfg} (hc : Q.WF c)
    (h : Q.qstep c = some c') : Q.WF c' := by
  simp only [QuadMachine.qstep, Option.map_eq_some_iff] at h
  obtain ⟨r, hr, hrc⟩ := h
  obtain ⟨q', y, mv⟩ := r
  have hy1 := Q.δ_write_pos hr
  have hy2 := Q.δ_write_le hr
  have hq := Q.δ_state_lt hr
  have htail : ∀ d ∈ c.front.tail, 1 ≤ d ∧ d ≤ Q.nsym := fun d hd =>
    hc.front_mem d (List.mem_of_mem_tail hd)
  cases mv
  · subst hrc
    refine ⟨?_, hc.back_mem, hq⟩
    intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · exact ⟨hy1, hy2⟩
    · exact htail d hd
  · subst hrc
    refine ⟨?_, htail, hq⟩
    intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · exact ⟨hy1, hy2⟩
    · exact hc.back_mem d hd

/-! ## The quadruple table, on the digits the simulation produces -/

@[simp] theorem lo_eq (n : ℕ) : Q.toModular.lo n = n % Q.m := rfl

@[simp] theorem hi_eq (n : ℕ) : Q.toModular.hi n = n / Q.m := rfl

theorem mod_tag_add {t : ℕ} (E : ℕ) (ht : t < Q.m) : (t + Q.m * E) % Q.m = t := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]

theorem div_tag_add {t : ℕ} (E : ℕ) (ht : t < Q.m) : (t + Q.m * E) / Q.m = E := by
  rw [Nat.add_mul_div_left _ _ Q.m_pos, Nat.div_eq_of_lt ht, Nat.zero_add]

theorem quadOf_simA {q s : ℕ} (hq : q < Q.nst) (hs : s ≤ Q.nsym) :
    Q.quadOf (Q.tagA q) s =
      (match Q.δ q s with
       | some (q', y, mv) => some (Q.simEmit q' y mv true)
       | none => some (Q.m + Q.tagB Q.e1, false)) := by
  have hp := Q.tagA_pos q
  have h1 : Q.tagA q < Q.m := Q.tagA_lt (by simp only [nstAll]; omega)
  have h2 : s < Q.m := Q.lt_m_of_le_nsym hs
  have h0 : ¬ (Q.tagA q = 0 ∧ s = 0) := by omega
  have h3 : ¬ (Q.tagA q = Q.tagA Q.e2) := by simp only [tagA, e2]; omega
  have h4 : ¬ (s = Q.tagB Q.e1) := by simp only [tagB, e1, nstAll]; omega
  have h5 : Q.isSimA (Q.tagA q) ∧ s ≤ Q.nsym := by
    refine ⟨⟨?_, ?_⟩, hs⟩ <;> simp only [tagA] <;> omega
  have h6 : Q.tagA q - (Q.nsym + 1) = q := by simp only [tagA]; omega
  unfold quadOf
  rw [if_neg h0, if_pos ⟨h1, h2⟩, if_neg h3, if_neg h4, if_pos h5, h6]

theorem quadOf_simB {q s : ℕ} (hq : q < Q.nst) (hs : s ≤ Q.nsym) :
    Q.quadOf s (Q.tagB q) =
      (match Q.δ q s with
       | some (q', y, mv) => some (Q.simEmit q' y mv false)
       | none => some (Q.m + Q.tagB Q.e1, false)) := by
  have hp := Q.tagB_pos q
  have h1 : s < Q.m := Q.lt_m_of_le_nsym hs
  have h2 : Q.tagB q < Q.m := Q.tagB_lt (by simp only [nstAll]; omega)
  have h0 : ¬ (s = 0 ∧ Q.tagB q = 0) := by omega
  have h3 : ¬ (s = Q.tagA Q.e2) := by simp only [tagA, e2]; omega
  have h4 : ¬ (Q.tagB q = Q.tagB Q.e1) := by simp only [tagB, e1]; omega
  have h5 : ¬ (Q.isSimA s ∧ Q.tagB q ≤ Q.nsym) := by
    rintro ⟨⟨hle, -⟩, -⟩; omega
  have h6 : Q.isSimB (Q.tagB q) ∧ s ≤ Q.nsym := by
    refine ⟨⟨?_, ?_⟩, hs⟩ <;> simp only [tagB] <;> omega
  have h7 : Q.tagB q - (Q.nsym + Q.nstAll + 1) = q := by simp only [tagB]; omega
  unfold quadOf
  rw [if_neg h0, if_pos ⟨h1, h2⟩, if_neg h3, if_neg h4, if_neg h5, if_pos h6, h7]

theorem quadOf_e2_zero : Q.quadOf (Q.tagA Q.e2) 0 = some (0, true) := by
  have hp := Q.tagA_pos Q.e2
  have h1 : Q.tagA Q.e2 < Q.m := Q.tagA_lt Q.e2_lt
  unfold quadOf
  rw [if_neg (by omega : ¬ (Q.tagA Q.e2 = 0 ∧ (0:ℕ) = 0)),
    if_pos ⟨h1, Q.m_pos⟩, if_pos rfl, if_pos rfl]

theorem quadOf_e2_pos {b : ℕ} (hb : 0 < b) (hbm : b < Q.m) :
    Q.quadOf (Q.tagA Q.e2) b = some (Q.tagA Q.e2, true) := by
  have hp := Q.tagA_pos Q.e2
  have h1 : Q.tagA Q.e2 < Q.m := Q.tagA_lt Q.e2_lt
  unfold quadOf
  rw [if_neg (by omega : ¬ (Q.tagA Q.e2 = 0 ∧ b = 0)),
    if_pos ⟨h1, hbm⟩, if_pos rfl, if_neg (by omega : ¬ (b = 0))]

theorem quadOf_e1_zero : Q.quadOf 0 (Q.tagB Q.e1) = some (Q.tagA Q.e2, true) := by
  have hp := Q.tagB_pos Q.e1
  have hA := Q.tagA_pos Q.e2
  have h1 : Q.tagB Q.e1 < Q.m := Q.tagB_lt Q.e1_lt
  unfold quadOf
  rw [if_neg (by omega : ¬ ((0:ℕ) = 0 ∧ Q.tagB Q.e1 = 0)),
    if_pos ⟨Q.m_pos, h1⟩, if_neg (by omega : ¬ ((0:ℕ) = Q.tagA Q.e2)),
    if_pos rfl, if_pos rfl]

theorem quadOf_e1_pos {a : ℕ} (ha : 0 < a) (ham : a < Q.m) (hne : a ≠ Q.tagA Q.e2) :
    Q.quadOf a (Q.tagB Q.e1) = some (a * Q.m + Q.tagB Q.e1, false) := by
  have hp := Q.tagB_pos Q.e1
  have h1 : Q.tagB Q.e1 < Q.m := Q.tagB_lt Q.e1_lt
  unfold quadOf
  rw [if_neg (by omega : ¬ (a = 0 ∧ Q.tagB Q.e1 = 0)),
    if_pos ⟨ham, h1⟩, if_neg hne, if_pos rfl, if_neg (by omega : ¬ (a = 0))]

/-! ## Erasure

A halting computation must end at `(0,0)`, so both stacks have to be emptied.
The transfer state `e1` moves `α` onto `β` one digit at a time; when `α` runs
out --- which is visible, because its digit reads `0` --- the drain state `e2`
empties `β` the same way, and when that runs out the machine is at `(0,0)`. -/

/-- The digits an erasing configuration may carry. -/
def CleanDigits (l : List ℕ) : Prop := ∀ d ∈ l, 1 ≤ d ∧ d ≤ Q.nsym + 1

theorem CleanDigits.lt_m {Q : QuadMachine} {l : List ℕ} (h : Q.CleanDigits l) :
    ∀ d ∈ l, d < Q.m :=
  fun d hd => by have := (h d hd).2; simp only [m, nstAll]; omega

theorem CleanDigits.ne_e2 {Q : QuadMachine} {l : List ℕ} (h : Q.CleanDigits l) :
    ∀ d ∈ l, d ≠ Q.tagA Q.e2 := by
  intro d hd
  have := (h d hd).2
  simp only [tagA, e2]
  omega

theorem CleanDigits.tail {Q : QuadMachine} {l : List ℕ} (h : Q.CleanDigits l) :
    Q.CleanDigits l.tail :=
  fun d hd => h d (List.mem_of_mem_tail hd)

/-- **The drain.**  From `(e2, R)` the machine empties `R` and stops at `(0,0)`. -/
theorem halts_drain : ∀ (R : List ℕ), Q.CleanDigits R →
    Q.toModular.Halts (Q.tagA Q.e2, encList Q.m R)
  | [], _ => by
      have h1 : Q.toModular.hi (Q.tagA Q.e2) = 0 := by
        rw [hi_eq, Nat.div_eq_of_lt (Q.tagA_lt Q.e2_lt)]
      have h2 : Q.toModular.hi (encList Q.m ([] : List ℕ)) = 0 := by
        rw [hi_eq, encList_nil, Nat.zero_div]
      have hq : Q.toModular.quad (Q.toModular.lo (Q.tagA Q.e2))
          (Q.toModular.lo (encList Q.m ([] : List ℕ))) = some (0, true) := by
        rw [lo_eq, lo_eq, encList_nil, Nat.zero_mod,
          Nat.mod_eq_of_lt (Q.tagA_lt Q.e2_lt), toModular_quad, quadOf_e2_zero]
      have hstep : Q.toModular.step (Q.tagA Q.e2, encList Q.m ([] : List ℕ))
          = some (0, 0) := by
        rw [Q.toModular.step_right hq, h1, h2, Nat.zero_mul, Nat.zero_add]
      exact Relation.ReflTransGen.single hstep
  | d :: R, h => by
      have hdm : d < Q.m := h.lt_m d (List.mem_cons_self ..)
      have hd1 : 1 ≤ d := (h d (List.mem_cons_self ..)).1
      have h1 : Q.toModular.hi (Q.tagA Q.e2) = 0 := by
        rw [hi_eq, Nat.div_eq_of_lt (Q.tagA_lt Q.e2_lt)]
      have h2 : Q.toModular.hi (encList Q.m (d :: R)) = encList Q.m R := by
        rw [hi_eq, encList_div Q.m_pos (fun x hx => h.lt_m x hx), List.tail_cons]
      have hq : Q.toModular.quad (Q.toModular.lo (Q.tagA Q.e2))
          (Q.toModular.lo (encList Q.m (d :: R))) = some (Q.tagA Q.e2, true) := by
        rw [lo_eq, lo_eq, Nat.mod_eq_of_lt (Q.tagA_lt Q.e2_lt),
          encList_mod (fun x hx => h.lt_m x hx), List.headI_cons, toModular_quad,
          Q.quadOf_e2_pos (by omega) hdm]
      have hstep : Q.toModular.step (Q.tagA Q.e2, encList Q.m (d :: R))
          = some (Q.tagA Q.e2, encList Q.m R) := by
        rw [Q.toModular.step_right hq, h1, h2, Nat.zero_mul, Nat.zero_add]
      exact Relation.ReflTransGen.head hstep
        (halts_drain R fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- **The transfer.**  From `(L, e1 · R)` the machine moves `L` onto `R` and
then drains, so it stops at `(0,0)`. -/
theorem halts_transfer : ∀ (L R : List ℕ), Q.CleanDigits L → Q.CleanDigits R →
    Q.toModular.Halts (encList Q.m L, Q.tagB Q.e1 + Q.m * encList Q.m R)
  | [], R, _, hR => by
      have h1 : Q.toModular.hi (encList Q.m ([] : List ℕ)) = 0 := by
        rw [hi_eq, encList_nil, Nat.zero_div]
      have h2 : Q.toModular.hi (Q.tagB Q.e1 + Q.m * encList Q.m R) = encList Q.m R := by
        rw [hi_eq]; exact Q.div_tag_add _ (Q.tagB_lt Q.e1_lt)
      have hq : Q.toModular.quad (Q.toModular.lo (encList Q.m ([] : List ℕ)))
          (Q.toModular.lo (Q.tagB Q.e1 + Q.m * encList Q.m R))
          = some (Q.tagA Q.e2, true) := by
        rw [lo_eq, lo_eq, encList_nil, Nat.zero_mod,
          Q.mod_tag_add _ (Q.tagB_lt Q.e1_lt), toModular_quad, quadOf_e1_zero]
      have hstep : Q.toModular.step (encList Q.m ([] : List ℕ),
          Q.tagB Q.e1 + Q.m * encList Q.m R) = some (Q.tagA Q.e2, encList Q.m R) := by
        rw [Q.toModular.step_right hq, h1, h2, Nat.zero_mul, Nat.zero_add]
      exact Relation.ReflTransGen.head hstep (Q.halts_drain R hR)
  | d :: L, R, hL, hR => by
      have hdm : d < Q.m := hL.lt_m d (List.mem_cons_self ..)
      have hdd : 1 ≤ d ∧ d ≤ Q.nsym + 1 := hL d (List.mem_cons_self ..)
      have hd1 : 1 ≤ d := hdd.1
      have h1 : Q.toModular.hi (encList Q.m (d :: L)) = encList Q.m L := by
        rw [hi_eq, encList_div Q.m_pos (fun x hx => hL.lt_m x hx), List.tail_cons]
      have h2 : Q.toModular.hi (Q.tagB Q.e1 + Q.m * encList Q.m R) = encList Q.m R := by
        rw [hi_eq]; exact Q.div_tag_add _ (Q.tagB_lt Q.e1_lt)
      have h3 : encList Q.m R * Q.m ^ 2 + (d * Q.m + Q.tagB Q.e1)
          = Q.tagB Q.e1 + Q.m * encList Q.m (d :: R) := by
        rw [encList_cons]; ring
      have hq : Q.toModular.quad (Q.toModular.lo (encList Q.m (d :: L)))
          (Q.toModular.lo (Q.tagB Q.e1 + Q.m * encList Q.m R))
          = some (d * Q.m + Q.tagB Q.e1, false) := by
        rw [lo_eq, lo_eq, encList_mod (fun x hx => hL.lt_m x hx), List.headI_cons,
          Q.mod_tag_add _ (Q.tagB_lt Q.e1_lt), toModular_quad,
          Q.quadOf_e1_pos (by omega) hdm (hL.ne_e2 d (List.mem_cons_self ..))]
      have hstep : Q.toModular.step (encList Q.m (d :: L),
            Q.tagB Q.e1 + Q.m * encList Q.m R)
          = some (encList Q.m L, Q.tagB Q.e1 + Q.m * encList Q.m (d :: R)) := by
        rw [Q.toModular.step_left hq, h1, h2, toModular_size, h3]
      refine Relation.ReflTransGen.head hstep
        (halts_transfer L (d :: R) (fun x hx => hL x (List.mem_cons_of_mem _ hx)) ?_)
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hdd
      · exact hR x hx

/-! ## One machine step is one modular-machine step -/

@[simp] theorem encCfg_true (back front : List ℕ) (q : ℕ) :
    Q.encCfg ⟨back, front, q, true⟩
      = (Q.tagA q + Q.m * encList Q.m back, encList Q.m front) := rfl

@[simp] theorem encCfg_false (back front : List ℕ) (q : ℕ) :
    Q.encCfg ⟨back, front, q, false⟩
      = (encList Q.m front, Q.tagB q + Q.m * encList Q.m back) := rfl

theorem tagA_lt_of_lt_nst {q : ℕ} (h : q < Q.nst) : Q.tagA q < Q.m :=
  Q.tagA_lt (by simp only [nstAll]; omega)

theorem tagB_lt_of_lt_nst {q : ℕ} (h : q < Q.nst) : Q.tagB q < Q.m :=
  Q.tagB_lt (by simp only [nstAll]; omega)

theorem WF.headI_le {Q : QuadMachine} {c : QCfg} (hc : Q.WF c) :
    c.front.headI ≤ Q.nsym := by
  cases hf : c.front with
  | nil => simp
  | cons d l =>
      have : d ∈ c.front := by rw [hf]; exact List.mem_cons_self ..
      simpa [hf] using (hc.front_mem d this).2

/-- **The simulation step.**  One step of the two-stack machine is one step of
the modular machine it induces. -/
theorem step_encCfg {c c' : QCfg} (hc : Q.WF c) (h : Q.qstep c = some c') :
    Q.toModular.step (Q.encCfg c) = some (Q.encCfg c') := by
  obtain ⟨back, front, q, side⟩ := c
  have hhead : front.headI ≤ Q.nsym := hc.headI_le
  have hq : q < Q.nst := hc.state_lt
  have hfm : ∀ d ∈ front, d < Q.m := hc.digits_lt.2
  have hlof : encList Q.m front % Q.m = front.headI := encList_mod hfm
  have hhif : encList Q.m front / Q.m = encList Q.m front.tail :=
    encList_div Q.m_pos hfm
  simp only [QuadMachine.qstep, Option.map_eq_some_iff] at h
  obtain ⟨r, hr, hrc⟩ := h
  obtain ⟨q', y, mv⟩ := r
  have hy2 := Q.δ_write_le hr
  have hq' := Q.δ_state_lt hr
  have hyQ : y < Q.m := Q.lt_m_of_le_nsym hy2
  have hA : Q.tagA q < Q.m := Q.tagA_lt_of_lt_nst hq
  have hB : Q.tagB q < Q.m := Q.tagB_lt_of_lt_nst hq
  cases mv <;> subst hrc <;> cases side
  · -- state on β, head turns around: an `R` quadruple, state moves to α
    show Q.toModular.step (Q.encCfg ⟨back, front, q, false⟩)
        = some (Q.encCfg ⟨y :: front.tail, back, q', true⟩)
    have harith : encList Q.m front.tail * Q.m ^ 2 + (y * Q.m + Q.tagA q')
        = Q.tagA q' + Q.m * encList Q.m (y :: front.tail) := by
      rw [encList_cons]; ring
    have hquad : Q.toModular.quad (Q.toModular.lo (encList Q.m front))
        (Q.toModular.lo (Q.tagB q + Q.m * encList Q.m back))
        = some (y * Q.m + Q.tagA q', true) := by
      rw [lo_eq, lo_eq, hlof, Q.mod_tag_add _ hB, toModular_quad,
        Q.quadOf_simB hq hhead, hr]
      rfl
    rw [encCfg_false, encCfg_true, Q.toModular.step_right hquad, hi_eq, hi_eq,
      hhif, Q.div_tag_add _ hB, toModular_size, harith]
  · -- state on α, head turns around: an `L` quadruple, state moves to β
    show Q.toModular.step (Q.encCfg ⟨back, front, q, true⟩)
        = some (Q.encCfg ⟨y :: front.tail, back, q', false⟩)
    have harith : encList Q.m front.tail * Q.m ^ 2 + (y * Q.m + Q.tagB q')
        = Q.tagB q' + Q.m * encList Q.m (y :: front.tail) := by
      rw [encList_cons]; ring
    have hquad : Q.toModular.quad (Q.toModular.lo (Q.tagA q + Q.m * encList Q.m back))
        (Q.toModular.lo (encList Q.m front))
        = some (y * Q.m + Q.tagB q', false) := by
      rw [lo_eq, lo_eq, hlof, Q.mod_tag_add _ hA, toModular_quad,
        Q.quadOf_simA hq hhead, hr]
      rfl
    rw [encCfg_true, encCfg_false, Q.toModular.step_left hquad, hi_eq, hi_eq,
      hhif, Q.div_tag_add _ hA, toModular_size, harith]
  · -- state on β, head moves on: an `L` quadruple, state stays on β
    have harith : encList Q.m back * Q.m ^ 2 + (y * Q.m + Q.tagB q')
        = Q.tagB q' + Q.m * encList Q.m (y :: back) := by
      rw [encList_cons]; ring
    have hquad : Q.toModular.quad (Q.toModular.lo (encList Q.m front))
        (Q.toModular.lo (Q.tagB q + Q.m * encList Q.m back))
        = some (y * Q.m + Q.tagB q', false) := by
      rw [lo_eq, lo_eq, hlof, Q.mod_tag_add _ hB, toModular_quad,
        Q.quadOf_simB hq hhead, hr]
      rfl
    rw [encCfg_false, encCfg_false, Q.toModular.step_left hquad, hi_eq, hi_eq,
      hhif, Q.div_tag_add _ hB, toModular_size, harith]
  · -- state on α, head moves on: an `R` quadruple, state stays on α
    have harith : encList Q.m back * Q.m ^ 2 + (y * Q.m + Q.tagA q')
        = Q.tagA q' + Q.m * encList Q.m (y :: back) := by
      rw [encList_cons]; ring
    have hquad : Q.toModular.quad (Q.toModular.lo (Q.tagA q + Q.m * encList Q.m back))
        (Q.toModular.lo (encList Q.m front))
        = some (y * Q.m + Q.tagA q', true) := by
      rw [lo_eq, lo_eq, hlof, Q.mod_tag_add _ hA, toModular_quad,
        Q.quadOf_simA hq hhead, hr]
      rfl
    rw [encCfg_true, encCfg_true, Q.toModular.step_right hquad, hi_eq, hi_eq,
      hhif, Q.div_tag_add _ hA, toModular_size, harith]

/-- **Entering the erasure.**  When the machine has no instruction, the modular
machine steps into the transfer configuration instead of getting stuck. -/
theorem step_encCfg_none {c : QCfg} (hc : Q.WF c) (h : Q.qstep c = none) :
    ∃ L R : List ℕ, Q.CleanDigits L ∧ Q.CleanDigits R ∧
      Q.toModular.step (Q.encCfg c)
        = some (encList Q.m L, Q.tagB Q.e1 + Q.m * encList Q.m R) := by
  obtain ⟨back, front, q, side⟩ := c
  have hhead : front.headI ≤ Q.nsym := hc.headI_le
  have hq : q < Q.nst := hc.state_lt
  have hbmem : ∀ d ∈ back, 1 ≤ d ∧ d ≤ Q.nsym := hc.back_mem
  have hfmem : ∀ d ∈ front, 1 ≤ d ∧ d ≤ Q.nsym := hc.front_mem
  have hfm : ∀ d ∈ front, d < Q.m := hc.digits_lt.2
  have hlof : encList Q.m front % Q.m = front.headI := encList_mod hfm
  have hhif : encList Q.m front / Q.m = encList Q.m front.tail :=
    encList_div Q.m_pos hfm
  have hA : Q.tagA q < Q.m := Q.tagA_lt_of_lt_nst hq
  have hB : Q.tagB q < Q.m := Q.tagB_lt_of_lt_nst hq
  have hδ : Q.δ q front.headI = none := by
    simpa [QuadMachine.qstep] using h
  have hbclean : Q.CleanDigits back := fun d hd =>
    ⟨(hbmem d hd).1, le_trans (hbmem d hd).2 (Nat.le_succ _)⟩
  have hfclean : Q.CleanDigits front.tail := fun d hd =>
    ⟨(hfmem d (List.mem_of_mem_tail hd)).1,
      le_trans (hfmem d (List.mem_of_mem_tail hd)).2 (Nat.le_succ _)⟩
  cases side
  · refine ⟨front.tail, 1 :: back, hfclean, ?_, ?_⟩
    · intro d hd
      rcases List.mem_cons.1 hd with rfl | hd
      · omega
      · exact hbclean d hd
    · have harith : encList Q.m back * Q.m ^ 2 + (Q.m + Q.tagB Q.e1)
          = Q.tagB Q.e1 + Q.m * encList Q.m (1 :: back) := by
        rw [encList_cons]; ring
      have hquad : Q.toModular.quad (Q.toModular.lo (encList Q.m front))
          (Q.toModular.lo (Q.tagB q + Q.m * encList Q.m back))
          = some (Q.m + Q.tagB Q.e1, false) := by
        rw [lo_eq, lo_eq, hlof, Q.mod_tag_add _ hB, toModular_quad,
          Q.quadOf_simB hq hhead, hδ]
      rw [encCfg_false, Q.toModular.step_left hquad, hi_eq, hi_eq, hhif,
        Q.div_tag_add _ hB, toModular_size, harith]
  · refine ⟨back, 1 :: front.tail, hbclean, ?_, ?_⟩
    · intro d hd
      rcases List.mem_cons.1 hd with rfl | hd
      · omega
      · exact hfclean d hd
    · have harith : encList Q.m front.tail * Q.m ^ 2 + (Q.m + Q.tagB Q.e1)
          = Q.tagB Q.e1 + Q.m * encList Q.m (1 :: front.tail) := by
        rw [encList_cons]; ring
      have hquad : Q.toModular.quad (Q.toModular.lo (Q.tagA q + Q.m * encList Q.m back))
          (Q.toModular.lo (encList Q.m front))
          = some (Q.m + Q.tagB Q.e1, false) := by
        rw [lo_eq, lo_eq, hlof, Q.mod_tag_add _ hA, toModular_quad,
          Q.quadOf_simA hq hhead, hδ]
      rw [encCfg_true, Q.toModular.step_left hquad, hi_eq, hi_eq, hhif,
        Q.div_tag_add _ hA, toModular_size, harith]

/-- **The machine halts, so the modular machine reaches `(0,0)`.** -/
theorem halts_encCfg_of_qstep_none {c : QCfg} (hc : Q.WF c) (h : Q.qstep c = none) :
    Q.toModular.Halts (Q.encCfg c) := by
  obtain ⟨L, R, hL, hR, hstep⟩ := Q.step_encCfg_none hc h
  exact Relation.ReflTransGen.head hstep (Q.halts_transfer L R hL hR)

/-! ## Halting

The modular machine reaches `(0,0)` from an encoded configuration exactly when
the two-stack machine runs out of instructions.  One direction is the
simulation followed by the erasure.  The other is determinism: from an encoded
configuration the only reachable configurations are encodings, and no encoding
is `(0,0)` --- the state digit is not zero. -/

/-- Iterating the machine. -/
def qsteps (Q : QuadMachine) : ℕ → QCfg → Option QCfg
  | 0, c => some c
  | n + 1, c => (Q.qstep c).bind (qsteps Q n)

@[simp] theorem qsteps_zero (c : QCfg) : Q.qsteps 0 c = some c := rfl

@[simp] theorem qsteps_succ (n : ℕ) (c : QCfg) :
    Q.qsteps (n + 1) c = (Q.qstep c).bind (Q.qsteps n) := rfl

/-- A run can be extended by one step at its end. -/
theorem qsteps_succ_end : ∀ (n : ℕ) {c c' c'' : QCfg},
    Q.qsteps n c = some c' → Q.qstep c' = some c'' → Q.qsteps (n + 1) c = some c''
  | 0, c, c', c'', h1, h2 => by
      obtain rfl : c = c' := Option.some.inj h1
      rw [qsteps_succ, h2]
      rfl
  | n + 1, c, c', c'', h1, h2 => by
      rw [qsteps_succ] at h1
      rcases hq : Q.qstep c with _ | c₁
      · rw [hq] at h1; exact absurd h1 (by simp)
      · rw [hq] at h1
        have h1' : Q.qsteps n c₁ = some c' := h1
        rw [qsteps_succ, hq]
        exact qsteps_succ_end n h1' h2

/-- **The machine halts**: after finitely many steps it has no instruction. -/
def QHalts (c : QCfg) : Prop := ∃ (n : ℕ) (c' : QCfg), Q.qsteps n c = some c' ∧ Q.qstep c' = none

theorem encCfg_ne_zero (c : QCfg) : Q.encCfg c ≠ (0, 0) := by
  obtain ⟨back, front, q, side⟩ := c
  cases side
  · rw [encCfg_false]
    intro hEq
    have h2 : Q.tagB q + Q.m * encList Q.m back = 0 := congrArg Prod.snd hEq
    have := Q.tagB_pos q
    omega
  · rw [encCfg_true]
    intro hEq
    have h1 : Q.tagA q + Q.m * encList Q.m back = 0 := congrArg Prod.fst hEq
    have := Q.tagA_pos q
    omega

theorem halts_encCfg_of_QHalts : ∀ (n : ℕ) {c c' : QCfg}, Q.WF c →
    Q.qsteps n c = some c' → Q.qstep c' = none → Q.toModular.Halts (Q.encCfg c)
  | 0, c, c', hc, h1, h2 => by
      have hcc : c = c' := Option.some.inj h1
      subst hcc
      exact Q.halts_encCfg_of_qstep_none hc h2
  | n + 1, c, c', hc, h1, h2 => by
      rw [qsteps_succ] at h1
      rcases hq : Q.qstep c with _ | c₁
      · rw [hq] at h1; exact absurd h1 (by simp)
      · rw [hq] at h1
        have h1' : Q.qsteps n c₁ = some c' := h1
        exact Relation.ReflTransGen.head (Q.step_encCfg hc hq)
          (halts_encCfg_of_QHalts n (hc.qstep hq) h1' h2)

theorem not_halts_encCfg_of_not_QHalts {c : QCfg} (hc : Q.WF c) (h : ¬ Q.QHalts c) :
    ¬ Q.toModular.Halts (Q.encCfg c) := by
  intro hhalt
  have key : ∀ p : ℕ × ℕ, Q.toModular.Reaches p (0, 0) →
      (∃ c' : QCfg, (∃ n, Q.qsteps n c = some c') ∧ Q.WF c' ∧ p = Q.encCfg c') →
      False := by
    intro p hp
    induction hp using Relation.ReflTransGen.head_induction_on with
    | refl =>
        rintro ⟨c', -, -, hpe⟩
        exact Q.encCfg_ne_zero c' hpe.symm
    | @head p₁ p₂ hstep _ ih =>
        rintro ⟨c', ⟨n, hn⟩, hwf, rfl⟩
        rcases hnext : Q.qstep c' with _ | c''
        · exact h ⟨n, c', hn, hnext⟩
        · have hs : Q.toModular.step (Q.encCfg c') = some (Q.encCfg c'') :=
            Q.step_encCfg hwf hnext
          have hstep' : Q.toModular.step (Q.encCfg c') = some p₂ := hstep
          rw [hs] at hstep'
          exact ih ⟨c'', ⟨n + 1, Q.qsteps_succ_end n hn hnext⟩, hwf.qstep hnext,
            (Option.some.inj hstep').symm⟩
  exact key _ hhalt ⟨c, ⟨0, rfl⟩, hc, rfl⟩

/-- **S9's machine half.**  The modular machine induced by a two-stack machine
halts on an encoded configuration exactly when the machine itself halts. -/
theorem halts_encCfg_iff {c : QCfg} (hc : Q.WF c) :
    Q.toModular.Halts (Q.encCfg c) ↔ Q.QHalts c := by
  constructor
  · intro hh
    by_contra hn
    exact Q.not_halts_encCfg_of_not_QHalts hc hn hh
  · rintro ⟨n, c', h1, h2⟩
    exact Q.halts_encCfg_of_QHalts n hc h1 h2

end QuadMachine
end Computability
end GroupApproximation
