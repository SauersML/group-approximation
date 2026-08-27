import Mathlib.Computability.RE
import Mathlib.Logic.Relation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Modular machines: the computational input to Novikov--Boone

This is the first module of the Novikov--Boone chain (step **D4** of the debt
ledger in `GroupApproximation.Computability.AdianRabinMarkovProperty`), which
that ledger records as item **(b)** of the literature input behind the
manuscript corollary `\label{cor:undecidable}` inside `sec:consequences` of
`non_mf_group_notes.tex` (the subsection
`\subsection{Undecidability of MF recognition}`; line numbers drift under
concurrent edit, so only the stable anchors are quoted).

## Which proof of Novikov--Boone this chain follows, and why

The classical route (Boone 1954--57, streamlined by Britton 1963; written up in
Lyndon--Schupp *Combinatorial Group Theory* IV.7, and in Rotman *An
Introduction to the Theory of Groups* Ch. 12 with van Kampen diagrams) builds a
four-stage HNN tower over a free group whose associated subgroups are described
by a long list of words, and then proves "Boone's Lemma" by a multi-page case
analysis.  It is not the cheapest route to formalize.

This development instead follows the **modular machine** proof of
S. Aanderaa and D. E. Cohen, *Modular machines I, II*, in `Word Problems II:
The Oxford Book` (S. I. Adian, W. W. Boone, G. Higman, eds.), Studies in Logic
and the Foundations of Mathematics 95, North-Holland 1980, pp. 1--18 and
19--28, in the fully written-out form of

> Stephen G. Simpson, *A Slick Proof of the Unsolvability of the Word Problem
> for Finitely Presented Groups*, draft of 18 May 2005,
> `https://sgslogic.net/t20/logic/seminar/050517.pdf`

whose Definitions 1--3, Lemma 5, Definition 6, Lemma 7 and Theorem 8 are the
skeleton of this chain.  In that proof the base group is
`G = ⟨t, x, y | xy = yx⟩`, there is **one** family of HNN stable letters (one
per machine quadruple, all with the same shape of associated subgroup) and then
**one** further stable letter `k`; correctness is three short lemmas.  Every
declaration below is named after the numbered item of Simpson's writeup that it
formalizes, so the correspondence can be checked line by line against the
source.

## What this module contains

Simpson's Definition 3 (modular machines) and the *only* three facts about
machines that the group construction consumes:

* `ModularMachine.halts_iff_of_step` --- one step of the machine does not change
  whether the configuration halts.  This is the determinism/termination fact
  that makes the halting set a *good* subgroup in the sense of Simpson's
  Definition 2, and it is used nowhere else.
* `ModularMachine.haltsZ_right_iff` and `ModularMachine.haltsZ_left_iff` ---
  the same fact transported to the integer index set `ℤ × ℤ` on which the free
  basis of the base group is indexed, in exactly the parametrised form
  (`(a + uM, b + vM) ↦ (c + uM², v)` resp. `(a + uM, b + vM) ↦ (u, c + vM²)`)
  in which the HNN associated isomorphisms will act on basis indices.

Nothing here is conditional, and nothing here is group theory.

## A repair to the source

Simpson's Definition 3 does **not** require the halting configuration `(0,0)` to
be terminal.  Without that, `halts_iff_of_step` is false in the forward
direction: if some quadruple begins with `(0,0)` then `(0,0)` halts but its
successor need not, and the good-subgroup argument for `T_M` (the paragraph
after Definition 6 in the source, "if `φᵢ(t(α,β)) = t(α₁,β₁)` … then
`(α,β) ∈ H_M ⟺ (α₁,β₁) ∈ H_M`") breaks.  The field `quad_zero_zero` below
supplies the missing requirement.  It costs nothing: in the Turing-machine
simulation of the source's Theorem 4 the configuration `(0,0)` is the halted
one and carries no quadruple.

The bound `c < M²` of Definition 3 is likewise load-bearing and is recorded as
`quad_lt`; it is what forces a *negative* parameter `u` to be sent to a
*negative* first coordinate in `haltsZ_right_iff`, which is how the integer
index map restricts to a bijection of the nonnegative quadrant.

## Determinism is definitional

Simpson requires "for each `(a,b)` there is at most one quadruple of `M`
beginning with `(a,b)`".  Here the quadruples are packaged as a *function*
`quad : ℕ → ℕ → Option (ℕ × Bool)`, so determinism holds by construction rather
than as a hypothesis, and `step` is a partial function rather than a relation.
The `Bool` records the direction: `true` is `R`, `false` is `L`.
-/

namespace GroupApproximation
namespace BooneGroup

/-- **Simpson, Definition 3.**  A *modular machine* is an integer `size > 1`
together with a finite deterministic set of quadruples `(a, b, c, R)` and
`(a, b, c, L)` with `size > a ≥ 0`, `size > b ≥ 0` and `size² > c ≥ 0`.

The quadruples are packaged as a function `quad`, which makes the source's
determinism requirement ("at most one quadruple beginning with `(a,b)`") hold by
construction; the direction `R`/`L` is `true`/`false`.  Finiteness of the
quadruple set is the pair of `quad_eq_none` fields.  The field
`quad_zero_zero` is the repair to the source discussed in the module
docstring. -/
structure ModularMachine where
  /-- The modulus `M` of the machine.  Simpson writes `M`. -/
  size : ℕ
  /-- The modulus exceeds `1`. -/
  one_lt_size : 1 < size
  /-- The quadruple table: `quad a b = some (c, d)` is the quadruple
  `(a, b, c, R)` when `d = true` and `(a, b, c, L)` when `d = false`. -/
  quad : ℕ → ℕ → Option (ℕ × Bool)
  /-- Only residues below the modulus carry quadruples (first coordinate). -/
  quad_eq_none_left : ∀ {a b : ℕ}, size ≤ a → quad a b = none
  /-- Only residues below the modulus carry quadruples (second coordinate). -/
  quad_eq_none_right : ∀ {a b : ℕ}, size ≤ b → quad a b = none
  /-- The written value of a quadruple is below `size²`. -/
  quad_lt : ∀ {a b c : ℕ} {d : Bool}, quad a b = some (c, d) → c < size ^ 2
  /-- The halting configuration `(0,0)` is terminal.  See the module
  docstring: this is required for `halts_iff_of_step` and is missing from the
  source's Definition 3. -/
  quad_zero_zero : quad 0 0 = none

namespace ModularMachine

variable (M : ModularMachine)

theorem size_pos : 0 < M.size := lt_trans Nat.zero_lt_one M.one_lt_size

theorem size_ne_zero : M.size ≠ 0 := M.size_pos.ne'

/-! ## Base-`size` digits -/

/-- The low digit of a natural number in base `size`. -/
def lo (n : ℕ) : ℕ := n % M.size

/-- The high part of a natural number in base `size`. -/
def hi (n : ℕ) : ℕ := n / M.size

theorem lo_lt (n : ℕ) : M.lo n < M.size := Nat.mod_lt _ M.size_pos

@[simp] theorem lo_zero : M.lo 0 = 0 := Nat.zero_mod _

@[simp] theorem hi_zero : M.hi 0 = 0 := Nat.zero_div _

theorem lo_add_mul {a u : ℕ} (ha : a < M.size) : M.lo (a + u * M.size) = a := by
  unfold lo
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]

theorem hi_add_mul {a u : ℕ} (ha : a < M.size) : M.hi (a + u * M.size) = u := by
  unfold hi
  rw [Nat.add_mul_div_right _ _ M.size_pos, Nat.div_eq_of_lt ha, Nat.zero_add]

/-! ## The transition function -/

/-- **Simpson, Definition 3, the relation `(α,β) ⟶ (α₁,β₁)`.**  Writing
`α = u·size + a` and `β = v·size + b` with `a, b < size`, the machine moves to
`(u·size² + c, v)` on a quadruple `(a,b,c,R)` and to `(u, v·size² + c)` on a
quadruple `(a,b,c,L)`; if there is no quadruple for `(a,b)` the machine is
stuck.  Determinism is definitional: this is a function. -/
def step (p : ℕ × ℕ) : Option (ℕ × ℕ) :=
  (M.quad (M.lo p.1) (M.lo p.2)).map fun q =>
    cond q.2 (M.hi p.1 * M.size ^ 2 + q.1, M.hi p.2)
      (M.hi p.1, M.hi p.2 * M.size ^ 2 + q.1)

theorem step_eq_none {α β : ℕ} (h : M.quad (M.lo α) (M.lo β) = none) :
    M.step (α, β) = none := by
  simp [step, h]

theorem step_right {α β c : ℕ} (h : M.quad (M.lo α) (M.lo β) = some (c, true)) :
    M.step (α, β) = some (M.hi α * M.size ^ 2 + c, M.hi β) := by
  simp [step, h]

theorem step_left {α β c : ℕ} (h : M.quad (M.lo α) (M.lo β) = some (c, false)) :
    M.step (α, β) = some (M.hi α, M.hi β * M.size ^ 2 + c) := by
  simp [step, h]

/-- The halting configuration is terminal. -/
@[simp] theorem step_zero_zero : M.step (0, 0) = none :=
  M.step_eq_none (by simpa using M.quad_zero_zero)

/-! ## Reachability and the halting set -/

/-- One step of the machine, as a relation. -/
def StepRel (p q : ℕ × ℕ) : Prop := M.step p = some q

/-- **Simpson, Definition 3, `(α,β) ⟶* (ᾱ,β̄)`.**  Reachability by a finite
computation. -/
def Reaches : ℕ × ℕ → ℕ × ℕ → Prop := Relation.ReflTransGen M.StepRel

/-- **Simpson, Theorem 4, the set `H_M`.**  A configuration *halts* when the
machine takes it to `(0,0)`. -/
def Halts (p : ℕ × ℕ) : Prop := M.Reaches p (0, 0)

/-- The halting set `H_M ⊆ ℕ²`. -/
def haltingSet : Set (ℕ × ℕ) := {p | M.Halts p}

@[simp] theorem mem_haltingSet {p : ℕ × ℕ} : p ∈ M.haltingSet ↔ M.Halts p := Iff.rfl

theorem halts_zero_zero : M.Halts (0, 0) := Relation.ReflTransGen.refl

/-- **The one machine fact the group construction consumes.**  A single step of
the machine does not change whether a configuration halts.

The backward direction is trivial reachability.  The forward direction is where
both determinism (`step` is a function) and terminality of `(0,0)`
(`quad_zero_zero`) are used: a halting computation out of `p` is either empty,
in which case `p = (0,0)` and `p` takes no step at all, or begins with the
unique step out of `p`, which is the given one. -/
theorem halts_iff_of_step {p q : ℕ × ℕ} (h : M.step p = some q) :
    M.Halts p ↔ M.Halts q := by
  constructor
  · intro hp
    rcases Relation.ReflTransGen.cases_head hp with heq | ⟨r, hr, hrest⟩
    · rw [heq, M.step_zero_zero] at h
      simp at h
    · have hrq : r = q := Option.some.inj (hr.symm.trans h)
      rw [hrq] at hrest
      exact hrest
  · intro hq
    exact Relation.ReflTransGen.head h hq

/-! ## The halting set on integer indices

The free basis of the base group of the Boone construction is indexed by
`ℤ × ℤ`, not by `ℕ × ℕ`, so the halting set has to be read there. -/

/-- The halting set, read inside `ℤ × ℤ`.  A pair of integers is in it when it
is a pair of naturals and that pair halts. -/
def HaltsZ (p : ℤ × ℤ) : Prop :=
  ∃ m n : ℕ, p = ((m : ℤ), (n : ℤ)) ∧ M.Halts (m, n)

/-- The halting set `H_M`, read inside `ℤ × ℤ`. -/
def haltingSetZ : Set (ℤ × ℤ) := {p | M.HaltsZ p}

@[simp] theorem mem_haltingSetZ {p : ℤ × ℤ} : p ∈ M.haltingSetZ ↔ M.HaltsZ p := Iff.rfl

@[simp] theorem haltsZ_natCast (m n : ℕ) :
    M.HaltsZ ((m : ℤ), (n : ℤ)) ↔ M.Halts (m, n) := by
  constructor
  · rintro ⟨m', n', hmn, hhalt⟩
    have h1 : (m : ℤ) = (m' : ℤ) := congrArg Prod.fst hmn
    have h2 : (n : ℤ) = (n' : ℤ) := congrArg Prod.snd hmn
    have h1' : m = m' := by exact_mod_cast h1
    have h2' : n = n' := by exact_mod_cast h2
    rw [h1', h2']
    exact hhalt
  · intro h
    exact ⟨m, n, rfl, h⟩

theorem not_haltsZ_of_neg_left {α β : ℤ} (h : α < 0) : ¬ M.HaltsZ (α, β) := by
  rintro ⟨m, n, hmn, -⟩
  have hα : α = (m : ℤ) := congrArg Prod.fst hmn
  omega

theorem not_haltsZ_of_neg_right {α β : ℤ} (h : β < 0) : ¬ M.HaltsZ (α, β) := by
  rintro ⟨m, n, hmn, -⟩
  have hβ : β = (n : ℤ) := congrArg Prod.snd hmn
  omega

/-- **Simpson, the displayed computation in the proof of Lemma 7, `R` case, at
the level of basis indices.**  For a right-moving quadruple `(a,b,c,R)`, the
index map `(a + u·size, b + v·size) ↦ (c + u·size², v)` preserves and reflects
membership in the halting set, for *all* integer parameters `u, v` --- including
negative ones, where both sides are false because `c < size²`. -/
theorem haltsZ_right_iff {a b c : ℕ} (ha : a < M.size) (hb : b < M.size)
    (h : M.quad a b = some (c, true)) (u v : ℤ) :
    M.HaltsZ ((a : ℤ) + u * (M.size : ℤ), (b : ℤ) + v * (M.size : ℤ)) ↔
      M.HaltsZ ((c : ℤ) + u * (M.size : ℤ) ^ 2, v) := by
  have hsize : (0 : ℤ) < (M.size : ℤ) := by exact_mod_cast M.size_pos
  have hsq : (0 : ℤ) < (M.size : ℤ) ^ 2 := pow_pos hsize 2
  have haZ : (a : ℤ) < (M.size : ℤ) := by exact_mod_cast ha
  have hbZ : (b : ℤ) < (M.size : ℤ) := by exact_mod_cast hb
  have hcZ : (c : ℤ) < (M.size : ℤ) ^ 2 := by exact_mod_cast M.quad_lt h
  by_cases hu : u < 0
  · have hu1 : u ≤ -1 := by omega
    have hmul : u * (M.size : ℤ) ≤ -1 * (M.size : ℤ) :=
      mul_le_mul_of_nonneg_right hu1 hsize.le
    have hmul2 : u * (M.size : ℤ) ^ 2 ≤ -1 * (M.size : ℤ) ^ 2 :=
      mul_le_mul_of_nonneg_right hu1 hsq.le
    refine iff_of_false (M.not_haltsZ_of_neg_left ?_) (M.not_haltsZ_of_neg_left ?_)
    · linarith
    · linarith
  replace hu : 0 ≤ u := not_lt.mp hu
  by_cases hv : v < 0
  · have hv1 : v ≤ -1 := by omega
    have hmul : v * (M.size : ℤ) ≤ -1 * (M.size : ℤ) :=
      mul_le_mul_of_nonneg_right hv1 hsize.le
    refine iff_of_false (M.not_haltsZ_of_neg_right ?_) (M.not_haltsZ_of_neg_right ?_)
    · linarith
    · linarith
  replace hv : 0 ≤ v := not_lt.mp hv
  obtain ⟨u', rfl⟩ : ∃ u' : ℕ, u = (u' : ℤ) :=
    ⟨u.toNat, (Int.toNat_of_nonneg hu).symm⟩
  obtain ⟨v', rfl⟩ : ∃ v' : ℕ, v = (v' : ℤ) :=
    ⟨v.toNat, (Int.toNat_of_nonneg hv).symm⟩
  have e1 : (a : ℤ) + (u' : ℤ) * (M.size : ℤ) = ((a + u' * M.size : ℕ) : ℤ) := by
    push_cast; ring
  have e2 : (b : ℤ) + (v' : ℤ) * (M.size : ℤ) = ((b + v' * M.size : ℕ) : ℤ) := by
    push_cast; ring
  have e3 : (c : ℤ) + (u' : ℤ) * (M.size : ℤ) ^ 2
      = ((u' * M.size ^ 2 + c : ℕ) : ℤ) := by
    push_cast; ring
  rw [e1, e2, e3, M.haltsZ_natCast, M.haltsZ_natCast]
  have hquad : M.quad (M.lo (a + u' * M.size)) (M.lo (b + v' * M.size))
      = some (c, true) := by
    rw [M.lo_add_mul ha, M.lo_add_mul hb]; exact h
  have hstep : M.step (a + u' * M.size, b + v' * M.size)
      = some (u' * M.size ^ 2 + c, v') := by
    rw [M.step_right hquad, M.hi_add_mul ha, M.hi_add_mul hb]
  exact M.halts_iff_of_step hstep

/-- **Simpson, the displayed computation in the proof of Lemma 7, `L` case, at
the level of basis indices.**  For a left-moving quadruple `(a,b,c,L)`, the
index map `(a + u·size, b + v·size) ↦ (u, c + v·size²)` preserves and reflects
membership in the halting set. -/
theorem haltsZ_left_iff {a b c : ℕ} (ha : a < M.size) (hb : b < M.size)
    (h : M.quad a b = some (c, false)) (u v : ℤ) :
    M.HaltsZ ((a : ℤ) + u * (M.size : ℤ), (b : ℤ) + v * (M.size : ℤ)) ↔
      M.HaltsZ (u, (c : ℤ) + v * (M.size : ℤ) ^ 2) := by
  have hsize : (0 : ℤ) < (M.size : ℤ) := by exact_mod_cast M.size_pos
  have hsq : (0 : ℤ) < (M.size : ℤ) ^ 2 := pow_pos hsize 2
  have haZ : (a : ℤ) < (M.size : ℤ) := by exact_mod_cast ha
  have hbZ : (b : ℤ) < (M.size : ℤ) := by exact_mod_cast hb
  have hcZ : (c : ℤ) < (M.size : ℤ) ^ 2 := by exact_mod_cast M.quad_lt h
  by_cases hu : u < 0
  · have hu1 : u ≤ -1 := by omega
    have hmul : u * (M.size : ℤ) ≤ -1 * (M.size : ℤ) :=
      mul_le_mul_of_nonneg_right hu1 hsize.le
    refine iff_of_false (M.not_haltsZ_of_neg_left ?_) (M.not_haltsZ_of_neg_left ?_)
    · linarith
    · linarith
  replace hu : 0 ≤ u := not_lt.mp hu
  by_cases hv : v < 0
  · have hv1 : v ≤ -1 := by omega
    have hmul : v * (M.size : ℤ) ≤ -1 * (M.size : ℤ) :=
      mul_le_mul_of_nonneg_right hv1 hsize.le
    have hmul2 : v * (M.size : ℤ) ^ 2 ≤ -1 * (M.size : ℤ) ^ 2 :=
      mul_le_mul_of_nonneg_right hv1 hsq.le
    refine iff_of_false (M.not_haltsZ_of_neg_right ?_) (M.not_haltsZ_of_neg_right ?_)
    · linarith
    · linarith
  replace hv : 0 ≤ v := not_lt.mp hv
  obtain ⟨u', rfl⟩ : ∃ u' : ℕ, u = (u' : ℤ) :=
    ⟨u.toNat, (Int.toNat_of_nonneg hu).symm⟩
  obtain ⟨v', rfl⟩ : ∃ v' : ℕ, v = (v' : ℤ) :=
    ⟨v.toNat, (Int.toNat_of_nonneg hv).symm⟩
  have e1 : (a : ℤ) + (u' : ℤ) * (M.size : ℤ) = ((a + u' * M.size : ℕ) : ℤ) := by
    push_cast; ring
  have e2 : (b : ℤ) + (v' : ℤ) * (M.size : ℤ) = ((b + v' * M.size : ℕ) : ℤ) := by
    push_cast; ring
  have e3 : (c : ℤ) + (v' : ℤ) * (M.size : ℤ) ^ 2
      = ((v' * M.size ^ 2 + c : ℕ) : ℤ) := by
    push_cast; ring
  rw [e1, e2, e3, M.haltsZ_natCast, M.haltsZ_natCast]
  have hquad : M.quad (M.lo (a + u' * M.size)) (M.lo (b + v' * M.size))
      = some (c, false) := by
    rw [M.lo_add_mul ha, M.lo_add_mul hb]; exact h
  have hstep : M.step (a + u' * M.size, b + v' * M.size)
      = some (u', v' * M.size ^ 2 + c) := by
    rw [M.step_left hquad, M.hi_add_mul ha, M.hi_add_mul hb]
  exact M.halts_iff_of_step hstep

/-! ## The one remaining external debt, recorded in prose only

Simpson's Theorem 4 --- *there is a modular machine whose halting set is not
computable* --- is proved by simulating a Turing machine, and is the one step of
the source left to the reader.  It is **not** proved here, and it is
deliberately **not stated** here either, in any form.  This project's standard
forbids Lean statements conditional on an unformalized input, and a predicate
whose only purpose is to become such a hypothesis is one in disguise.  The debt
is recorded as prose:

> **DEBT (external, not formalized).**  No declaration anywhere in this chain
> asserts, assumes, or names as a hypothesis the existence of a modular machine
> with non-computable halting set.  Until that is a proved theorem, the chain
> establishes the *biconditional correctness* of the Boone construction --- for
> an **arbitrary** modular machine, a specific group word is trivial exactly
> when the configuration halts --- and stops there.  The undecidability
> capstone is a two-line corollary of that biconditional together with
> Simpson's Theorem 4, and must not be written before Theorem 4 exists.

Theorem 4 is a statement about modular machines alone: no group theory and no
semigroup theory enters it, so it is cleanly separable from everything the
group-theoretic modules do. -/

end ModularMachine

end BooneGroup
end GroupApproximation
