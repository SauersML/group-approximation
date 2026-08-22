import GroupApproximation.Higman.EnumeratedRangeTrace

/-!
# Addition, by running the transition device as a recursion

`Seq.higmanGenerated_transitionSet` turns a bounded-arity relation between
adjacent blocks into a condition imposed at every block of the index line, and
`Seq.higmanGenerated_of_transitionProjection` reads the first track of such a
trace off with `θᵗ`.  Everything in that pair is proved.  What has never been
done in this repository is to *run* it: to exhibit one genuine computation in
the format and identify its projection.

This module does that for the smallest interesting computation, the graph

    { (x, y, z) : z = x + y }

read as an arity-three relation --- the sequences supported on `[0, 3)` whose
third entry is the sum of the first two.  It is Higman's Lemma 2.4 at its base
case, and it is the prototype for the general primitive recursion.

## The format

Blocks of width eight, so `θ³` reads the first track.  Block `i` occupies the
coordinates `8i` to `8i+7` and carries

* `8i`   --- the **value** track `V`, the one the projection reads;
* `8i+1` --- a carried copy `Y` of the recursion variable;
* `8i+2` --- a carried copy `Z` of the answer;
* `8i+3` --- the **counter** `C`;
* `8i+4` --- the **running value** `W`.

The remaining three tracks are unconstrained, and the projection never sees
them.

## Why the counter may run in either direction

The recursion is on `y`, and `y` ranges over all of `ℤ`.  A trace whose counter
only climbs reaches the blocks `0, 1, …` and so computes `x + y` for `y ≥ 0`
only.  The repair is not a second construction but a second *mode*: the step
relation is the union of a climbing mode and a descending mode, and the two are
tied together by making `C` and `W` move in step.  The quantity `W - C` is then
invariant along a run whichever mode each individual step chooses --- monotonicity
of the counter is never needed and is never proved --- and the run finishes when
the counter meets the carried `Y`, at which point `W - C = x` and `W = Z` and
`C = Y` give `z = x + y` outright.  This is `addRunning_invariant` together with
`addTrace_eq`.

## Why the marker of `Higman/EnumeratedRangeTrace.lean` is not needed here

That module has to mark the block where a *counter reads zero*, because the
window of an arbitrary enumerated sequence may sit anywhere on the line.  Here
the window may be pinned at the origin: the trace is required to vanish on the
negative coordinates (`Seq.vanishBelow`, generated), the computation starts at
block `0`, and the answer is read at blocks `0`, `1`, `2`.  A one-sided trace
suffices because the *positions* the recursion visits are indices, not values,
and the value `y` is carried on a track rather than encoded as a length.

A trace may still restart after it has stopped, and nothing forbids it.  The
soundness argument never excludes restarts: it takes the **first** step that is
not a running step (`exists_addStop`), and both ways for a step to fail to be a
running one --- stopping, and idling --- deliver the equation.  Finite support is
what makes such a first step exist, and that is the only place finiteness is
used.

## What is assumed

Two families of arity-two relations, `Seq.eqCoord` and `Seq.succCoord`:

* `eqCoord d₁ d₂ = {f | f d₁ = f d₂}`,
* `succCoord d₁ d₂ = {f | f d₂ = f d₁ + 1}`,

each with every other coordinate free.  These are the variable calculus and the
successor atom of Higman's Section 2 --- `succCoord` is the base case `S` placed
at two coordinates, `eqCoord` is the diagonal placed at two coordinates --- and
they enter every theorem below as the named hypotheses `hEq` and `hSucc`.
Nothing else about the family is used: the trace itself is built from
`Seq.pinAt`, `Seq.vanishBelow` and `Seq.windowSupport`, all of which are already
unconditional.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

/-! ## 1.  The two coordinate relations that are assumed -/

/-- Two coordinates carry the same value; every other coordinate is free. -/
def eqCoord (d₁ d₂ : ℤ) : Set E := {f | f d₁ = f d₂}

/-- The coordinate `d₂` carries the successor of the coordinate `d₁`; every
other coordinate is free.  This is Higman's `S` placed at two coordinates. -/
def succCoord (d₁ d₂ : ℤ) : Set E := {f | f d₂ = f d₁ + 1}

/-! ## 2.  The five tracks -/

/-- The carried copy of the recursion variable, at block `i`. -/
def addY (g : E) (i : ℤ) : ℤ := g (8 * i + 1)

/-- The carried copy of the answer, at block `i`. -/
def addZ (g : E) (i : ℤ) : ℤ := g (8 * i + 2)

/-- The counter, at block `i`. -/
def addC (g : E) (i : ℤ) : ℤ := g (8 * i + 3)

/-- The running value, at block `i`. -/
def addW (g : E) (i : ℤ) : ℤ := g (8 * i + 4)

/-! ## 3.  The step relation, the anchor, and the trace -/

/-- The climbing mode: the carried data are copied and the counter and the
running value both advance. -/
def addRun : Set E := eqCoord 9 1 ∩ eqCoord 10 2 ∩ succCoord 3 11 ∩ succCoord 4 12

/-- The descending mode: the carried data are copied and the counter and the
running value both retreat. -/
def addBack : Set E := eqCoord 9 1 ∩ eqCoord 10 2 ∩ succCoord 11 3 ∩ succCoord 12 4

/-- The stopping step: the counter has met the carried recursion variable, the
running value has met the carried answer, and the next block is blank. -/
def addStop : Set E :=
  eqCoord 3 1 ∩ eqCoord 4 2 ∩ pinAt 9 0 ∩ pinAt 10 0 ∩ pinAt 11 0 ∩ pinAt 12 0

/-- The idle step: the block on the left is blank. -/
def addIdle : Set E := pinAt 1 0 ∩ pinAt 2 0 ∩ pinAt 3 0 ∩ pinAt 4 0

/-- **The relation between adjacent blocks.** -/
def addStep : Set E := addRun ∪ addBack ∪ addStop ∪ addIdle

/-- **The global conditions.**  The trace is one-sided, the counter starts at
zero, and the value track carries `x`, `y`, `z` at the blocks `0`, `1`, `2`. -/
def addAnchor : Set E :=
  vanishBelow 0 ∩ pinAt 3 0 ∩ eqCoord 4 0 ∩ eqCoord 8 1 ∩ eqCoord 16 2

/-- The traces. -/
def addTrace : Set E := transitionSet 8 addStep ∩ addAnchor

/-- The value track of a trace, read off by `θ³`. -/
def addProj : Set E := {f : E | ∃ g ∈ addTrace, ∀ i : ℤ, f i = g (8 * i)}

/-- **The graph of addition, as an arity-three relation.** -/
def addGraph : Set E :=
  {f : E | (∀ i : ℤ, i < 0 → f i = 0) ∧ (∀ i : ℤ, 3 ≤ i → f i = 0) ∧ f 2 = f 0 + f 1}

/-! ## 4.  The step relation is generated -/

theorem higmanGenerated_addRun (hEq : ∀ d₁ d₂ : ℤ, HigmanGenerated (eqCoord d₁ d₂))
    (hSucc : ∀ d₁ d₂ : ℤ, HigmanGenerated (succCoord d₁ d₂)) : HigmanGenerated addRun :=
  HigmanGenerated.inter
    (HigmanGenerated.inter (HigmanGenerated.inter (hEq 9 1) (hEq 10 2)) (hSucc 3 11))
    (hSucc 4 12)

theorem higmanGenerated_addBack (hEq : ∀ d₁ d₂ : ℤ, HigmanGenerated (eqCoord d₁ d₂))
    (hSucc : ∀ d₁ d₂ : ℤ, HigmanGenerated (succCoord d₁ d₂)) : HigmanGenerated addBack :=
  HigmanGenerated.inter
    (HigmanGenerated.inter (HigmanGenerated.inter (hEq 9 1) (hEq 10 2)) (hSucc 11 3))
    (hSucc 12 4)

theorem higmanGenerated_addStop (hEq : ∀ d₁ d₂ : ℤ, HigmanGenerated (eqCoord d₁ d₂)) :
    HigmanGenerated addStop :=
  HigmanGenerated.inter
    (HigmanGenerated.inter
      (HigmanGenerated.inter
        (HigmanGenerated.inter (HigmanGenerated.inter (hEq 3 1) (hEq 4 2))
          (higmanGenerated_pinAt 9 0))
        (higmanGenerated_pinAt 10 0))
      (higmanGenerated_pinAt 11 0))
    (higmanGenerated_pinAt 12 0)

theorem higmanGenerated_addIdle : HigmanGenerated addIdle :=
  HigmanGenerated.inter
    (HigmanGenerated.inter
      (HigmanGenerated.inter (higmanGenerated_pinAt 1 0) (higmanGenerated_pinAt 2 0))
      (higmanGenerated_pinAt 3 0))
    (higmanGenerated_pinAt 4 0)

theorem higmanGenerated_addStep (hEq : ∀ d₁ d₂ : ℤ, HigmanGenerated (eqCoord d₁ d₂))
    (hSucc : ∀ d₁ d₂ : ℤ, HigmanGenerated (succCoord d₁ d₂)) : HigmanGenerated addStep :=
  HigmanGenerated.union
    (HigmanGenerated.union
      (HigmanGenerated.union (higmanGenerated_addRun hEq hSucc)
        (higmanGenerated_addBack hEq hSucc))
      (higmanGenerated_addStop hEq))
    higmanGenerated_addIdle

theorem higmanGenerated_addAnchor (hEq : ∀ d₁ d₂ : ℤ, HigmanGenerated (eqCoord d₁ d₂)) :
    HigmanGenerated addAnchor :=
  HigmanGenerated.inter
    (HigmanGenerated.inter
      (HigmanGenerated.inter
        (HigmanGenerated.inter (higmanGenerated_vanishBelow 0) (higmanGenerated_pinAt 3 0))
        (hEq 4 0))
      (hEq 8 1))
    (hEq 16 2)

/-- **The value track of a trace is generated.**  This is the transition device
and the `θ³` projection, with no correctness content at all. -/
theorem higmanGenerated_addProj (hEq : ∀ d₁ d₂ : ℤ, HigmanGenerated (eqCoord d₁ d₂))
    (hSucc : ∀ d₁ d₂ : ℤ, HigmanGenerated (succCoord d₁ d₂)) : HigmanGenerated addProj := by
  refine higmanGenerated_of_transitionProjection (t := 3) (k := 8) (by norm_num)
    (higmanGenerated_addStep hEq hSucc) (higmanGenerated_addAnchor hEq) ?_
  intro f
  rw [show ((2 : ℤ) ^ (3 : ℕ)) = 8 from by norm_num]
  exact Iff.rfl

/-! ## 5.  Reading a pair of adjacent blocks -/

/-- The window of the transition device, evaluated. -/
theorem windowAt_eight_eval (g : E) (r j : ℤ) (h0 : 0 ≤ j) (hj : j < 16) :
    windowAt (2 * 8) (((8 : ℕ) : ℤ) * r) g j = g (8 * r + j) := by
  have hc16 : ((2 * 8 : ℕ) : ℤ) = 16 := by norm_num
  have hc8 : ((8 : ℕ) : ℤ) = 8 := by norm_num
  have hmem : j ∈ Finset.Ico (0 : ℤ) ((2 * 8 : ℕ) : ℤ) := by
    rw [Finset.mem_Ico, hc16]
    exact ⟨h0, hj⟩
  rw [windowAt_apply, if_pos hmem, hc8]

/-- A running step: the carried data are copied and the counter and the running
value move together, in one direction or the other. -/
def addRunning (g : E) (r : ℤ) : Prop :=
  (addY g (r + 1) = addY g r ∧ addZ g (r + 1) = addZ g r ∧
      addC g (r + 1) = addC g r + 1 ∧ addW g (r + 1) = addW g r + 1) ∨
    (addY g (r + 1) = addY g r ∧ addZ g (r + 1) = addZ g r ∧
      addC g r = addC g (r + 1) + 1 ∧ addW g r = addW g (r + 1) + 1)

/-- A stopping step. -/
def addStopped (g : E) (r : ℤ) : Prop :=
  addC g r = addY g r ∧ addW g r = addZ g r ∧ addY g (r + 1) = 0 ∧ addZ g (r + 1) = 0 ∧
    addC g (r + 1) = 0 ∧ addW g (r + 1) = 0

/-- An idle step. -/
def addIdled (g : E) (r : ℤ) : Prop :=
  addY g r = 0 ∧ addZ g r = 0 ∧ addC g r = 0 ∧ addW g r = 0

/-- **The step relation, read on the tracks.** -/
theorem mem_addStep_window (g : E) (r : ℤ) :
    windowAt (2 * 8) (((8 : ℕ) : ℤ) * r) g ∈ addStep ↔
      addRunning g r ∨ addStopped g r ∨ addIdled g r := by
  have h1 : windowAt (2 * 8) (((8 : ℕ) : ℤ) * r) g 1 = g (8 * r + 1) :=
    windowAt_eight_eval g r 1 (by omega) (by omega)
  have h2 : windowAt (2 * 8) (((8 : ℕ) : ℤ) * r) g 2 = g (8 * r + 2) :=
    windowAt_eight_eval g r 2 (by omega) (by omega)
  have h3 : windowAt (2 * 8) (((8 : ℕ) : ℤ) * r) g 3 = g (8 * r + 3) :=
    windowAt_eight_eval g r 3 (by omega) (by omega)
  have h4 : windowAt (2 * 8) (((8 : ℕ) : ℤ) * r) g 4 = g (8 * r + 4) :=
    windowAt_eight_eval g r 4 (by omega) (by omega)
  have h9 : windowAt (2 * 8) (((8 : ℕ) : ℤ) * r) g 9 = g (8 * (r + 1) + 1) := by
    have e : (8 : ℤ) * (r + 1) + 1 = 8 * r + 9 := by ring
    rw [windowAt_eight_eval g r 9 (by omega) (by omega), e]
  have h10 : windowAt (2 * 8) (((8 : ℕ) : ℤ) * r) g 10 = g (8 * (r + 1) + 2) := by
    have e : (8 : ℤ) * (r + 1) + 2 = 8 * r + 10 := by ring
    rw [windowAt_eight_eval g r 10 (by omega) (by omega), e]
  have h11 : windowAt (2 * 8) (((8 : ℕ) : ℤ) * r) g 11 = g (8 * (r + 1) + 3) := by
    have e : (8 : ℤ) * (r + 1) + 3 = 8 * r + 11 := by ring
    rw [windowAt_eight_eval g r 11 (by omega) (by omega), e]
  have h12 : windowAt (2 * 8) (((8 : ℕ) : ℤ) * r) g 12 = g (8 * (r + 1) + 4) := by
    have e : (8 : ℤ) * (r + 1) + 4 = 8 * r + 12 := by ring
    rw [windowAt_eight_eval g r 12 (by omega) (by omega), e]
  simp only [addStep, addRun, addBack, addStop, addIdle, addRunning, addStopped, addIdled,
    addY, addZ, addC, addW, eqCoord, succCoord, pinAt, Set.mem_union, Set.mem_inter_iff,
    Set.mem_setOf_eq, h1, h2, h3, h4, h9, h10, h11, h12]
  tauto

theorem addStep_cases {g : E} (hg : g ∈ transitionSet 8 addStep) (r : ℤ) :
    addRunning g r ∨ addStopped g r ∨ addIdled g r := (mem_addStep_window g r).mp (hg r)

/-! ## 6.  Soundness: a trace computes a sum -/

/-- **A run cannot go on for ever.**  A running step changes the counter, so a
counter that runs for ever is nonzero at infinitely many blocks, and a sequence
has finite support. -/
theorem exists_addStop (g : E) :
    ∃ n : ℕ, (∀ k : ℕ, k < n → addRunning g (k : ℤ)) ∧ ¬ addRunning g (n : ℤ) := by
  classical
  have hex : ∃ n : ℕ, ¬ addRunning g (n : ℤ) := by
    obtain ⟨_a, b, _ha, hb⟩ := exists_support_bounds g
    refine ⟨b.toNat + 1, ?_⟩
    intro hrun
    have hgt : b < ((b.toNat + 1 : ℕ) : ℤ) := by omega
    have hc0 : addC g ((b.toNat + 1 : ℕ) : ℤ) = 0 :=
      hb (8 * ((b.toNat + 1 : ℕ) : ℤ) + 3) (by omega)
    have hc1 : addC g (((b.toNat + 1 : ℕ) : ℤ) + 1) = 0 :=
      hb (8 * (((b.toNat + 1 : ℕ) : ℤ) + 1) + 3) (by omega)
    rcases hrun with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> omega
  exact ⟨Nat.find hex, fun k hk => not_not.mp (Nat.find_min hex hk), Nat.find_spec hex⟩

/-- **What a run preserves.**  The carried data are unchanged and the difference
of the running value and the counter is unchanged; the counter itself need not
be monotone. -/
theorem addRunning_invariant {g : E} {n : ℕ} (hrun : ∀ k : ℕ, k < n → addRunning g (k : ℤ)) :
    ∀ k : ℕ, k ≤ n → addY g (k : ℤ) = addY g ((0 : ℕ) : ℤ) ∧
      addZ g (k : ℤ) = addZ g ((0 : ℕ) : ℤ) ∧
      addW g (k : ℤ) - addC g (k : ℤ) = addW g ((0 : ℕ) : ℤ) - addC g ((0 : ℕ) : ℤ) := by
  intro k
  induction k with
  | zero =>
      intro _
      exact ⟨rfl, rfl, rfl⟩
  | succ j ih =>
      intro hj
      obtain ⟨i1, i2, i3⟩ := ih (by omega)
      have hcast : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by omega
      rw [hcast]
      rcases hrun j (by omega) with ⟨s1, s2, s3, s4⟩ | ⟨s1, s2, s3, s4⟩ <;>
        exact ⟨by omega, by omega, by omega⟩

/-- **The equation a trace certifies.**  The value track at the blocks `0`, `1`
and `2` satisfies `z = x + y`. -/
theorem addTrace_eq {g : E} (hg : g ∈ addTrace) : g 16 = g 0 + g 8 := by
  obtain ⟨hT, hA⟩ := hg
  have hc0 : g 3 = 0 := hA.1.1.1.2
  have hw0 : g 4 = g 0 := hA.1.1.2
  have hy0 : g 8 = g 1 := hA.1.2
  have hz0 : g 16 = g 2 := hA.2
  have e1 : addY g ((0 : ℕ) : ℤ) = g 1 := by
    show g (8 * ((0 : ℕ) : ℤ) + 1) = g 1
    norm_num
  have e2 : addZ g ((0 : ℕ) : ℤ) = g 2 := by
    show g (8 * ((0 : ℕ) : ℤ) + 2) = g 2
    norm_num
  have e3 : addC g ((0 : ℕ) : ℤ) = g 3 := by
    show g (8 * ((0 : ℕ) : ℤ) + 3) = g 3
    norm_num
  have e4 : addW g ((0 : ℕ) : ℤ) = g 4 := by
    show g (8 * ((0 : ℕ) : ℤ) + 4) = g 4
    norm_num
  obtain ⟨n, hrun, hstop⟩ := exists_addStop g
  obtain ⟨i1, i2, i3⟩ := addRunning_invariant hrun n le_rfl
  rw [hz0, hy0, ← hw0]
  rcases addStep_cases hT (n : ℤ) with hr | hs | hi
  · exact absurd hr hstop
  · obtain ⟨s1, s2, -, -, -, -⟩ := hs
    omega
  · obtain ⟨d1, d2, d3, d4⟩ := hi
    omega

/-! ## 7.  The trace of a given sum -/

/-- The counter of the constructed trace at block `q`: it climbs when the
recursion variable is non-negative and descends when it is negative, so that it
reads `y` after `|y|` blocks either way. -/
def addCount (y q : ℤ) : ℤ := if 0 ≤ y then q else -q

theorem addCount_zero (y : ℤ) : addCount y 0 = 0 := by
  simp only [addCount]
  rcases le_or_lt 0 y with h | h
  · rw [if_pos h]
  · rw [if_neg (by omega : ¬ (0 : ℤ) ≤ y), neg_zero]

theorem addCount_len (y : ℤ) : addCount y ((y.natAbs : ℤ)) = y := by
  simp only [addCount]
  rcases le_or_lt 0 y with h | h
  · rw [if_pos h]
    omega
  · rw [if_neg (by omega : ¬ (0 : ℤ) ≤ y)]
    omega

theorem addCount_up (y q : ℤ) (h : 0 ≤ y) : addCount y (q + 1) = addCount y q + 1 := by
  simp only [addCount]
  rw [if_pos h, if_pos h]

theorem addCount_down (y q : ℤ) (h : y < 0) : addCount y q = addCount y (q + 1) + 1 := by
  have h' : ¬ (0 : ℤ) ≤ y := by omega
  simp only [addCount]
  rw [if_neg h', if_neg h']
  ring

/-- The entry at track `d` of block `q` of the constructed trace. -/
def addEntry (x y z q d : ℤ) : ℤ :=
  if d = 0 then (if q = 0 then x else if q = 1 then y else if q = 2 then z else 0)
  else if (y.natAbs : ℤ) < q then 0
  else if d = 1 then y
  else if d = 2 then z
  else if d = 3 then addCount y q
  else if d = 4 then x + addCount y q
  else 0

theorem addEntry_val_zero (x y z : ℤ) : addEntry x y z 0 0 = x := by simp [addEntry]

theorem addEntry_val_one (x y z : ℤ) : addEntry x y z 1 0 = y := by simp [addEntry]

theorem addEntry_val_two (x y z : ℤ) : addEntry x y z 2 0 = z := by simp [addEntry]

theorem addEntry_val_other (x y z q : ℤ) (h0 : q ≠ 0) (h1 : q ≠ 1) (h2 : q ≠ 2) :
    addEntry x y z q 0 = 0 := by simp [addEntry, h0, h1, h2]

theorem addEntry_y (x y z q : ℤ) (hq : q ≤ (y.natAbs : ℤ)) : addEntry x y z q 1 = y := by
  have h : ¬ ((y.natAbs : ℤ) < q) := by omega
  simp [addEntry, h]

theorem addEntry_z (x y z q : ℤ) (hq : q ≤ (y.natAbs : ℤ)) : addEntry x y z q 2 = z := by
  have h : ¬ ((y.natAbs : ℤ) < q) := by omega
  simp [addEntry, h]

theorem addEntry_c (x y z q : ℤ) (hq : q ≤ (y.natAbs : ℤ)) :
    addEntry x y z q 3 = addCount y q := by
  have h : ¬ ((y.natAbs : ℤ) < q) := by omega
  simp [addEntry, h]

theorem addEntry_w (x y z q : ℤ) (hq : q ≤ (y.natAbs : ℤ)) :
    addEntry x y z q 4 = x + addCount y q := by
  have h : ¬ ((y.natAbs : ℤ) < q) := by omega
  simp [addEntry, h]

theorem addEntry_far (x y z q d : ℤ) (hq : (y.natAbs : ℤ) < q) (hd : d ≠ 0) :
    addEntry x y z q d = 0 := by simp [addEntry, hq, hd]

/-- The constructed trace, as a function on the index line. -/
def addFun (x y z i : ℤ) : ℤ := if i < 0 then 0 else addEntry x y z (i / 8) (i % 8)

theorem addFun_neg (x y z i : ℤ) (hi : i < 0) : addFun x y z i = 0 := by
  simp only [addFun]
  rw [if_pos hi]

theorem addFun_block (x y z q d : ℤ) (hq : 0 ≤ q) (hd0 : 0 ≤ d) (hd8 : d < 8) :
    addFun x y z (8 * q + d) = addEntry x y z q d := by
  have hi : ¬ (8 * q + d < 0) := by omega
  have hdiv : (8 * q + d) / 8 = q := by omega
  have hmod : (8 * q + d) % 8 = d := by omega
  simp only [addFun]
  rw [if_neg hi, hdiv, hmod]

theorem addFun_block_neg (x y z q d : ℤ) (hq : q < 0) (hd8 : d < 8) :
    addFun x y z (8 * q + d) = 0 := addFun_neg x y z (8 * q + d) (by omega)

theorem addFun_far (x y z i : ℤ) (hi : 8 * ((y.natAbs : ℤ) + 4) ≤ i) : addFun x y z i = 0 := by
  have h0 : ¬ (i < 0) := by omega
  have hq : (y.natAbs : ℤ) < i / 8 := by omega
  simp only [addFun]
  rw [if_neg h0]
  rcases eq_or_ne (i % 8) 0 with hd | hd
  · rw [hd]
    have h1 : i / 8 ≠ 0 := by omega
    have h2 : i / 8 ≠ 1 := by omega
    have h3 : i / 8 ≠ 2 := by omega
    exact addEntry_val_other x y z (i / 8) h1 h2 h3
  · exact addEntry_far x y z (i / 8) (i % 8) hq hd

theorem addFun_mem_Ico (x y z i : ℤ) (h : addFun x y z i ≠ 0) :
    i ∈ Finset.Ico (0 : ℤ) (8 * ((y.natAbs : ℤ) + 4)) := by
  rw [Finset.mem_Ico]
  rcases lt_or_le i 0 with hlt | hge
  · exact absurd (addFun_neg x y z i hlt) h
  · refine ⟨hge, ?_⟩
    rcases lt_or_le i (8 * ((y.natAbs : ℤ) + 4)) with hlt2 | hge2
    · exact hlt2
    · exact absurd (addFun_far x y z i hge2) h

/-- **The trace of the sum `z = x + y`.** -/
noncomputable def addWitness (x y z : ℤ) : E :=
  Finsupp.onFinset (Finset.Ico (0 : ℤ) (8 * ((y.natAbs : ℤ) + 4))) (addFun x y z)
    fun i hi => addFun_mem_Ico x y z i hi

theorem addWitness_apply (x y z i : ℤ) : addWitness x y z i = addFun x y z i := by
  simp only [addWitness, Finsupp.onFinset_apply]

theorem addWitness_coord (x y z q d i : ℤ) (hq : 0 ≤ q) (hd0 : 0 ≤ d) (hd8 : d < 8)
    (hi : i = 8 * q + d) : addWitness x y z i = addEntry x y z q d := by
  subst hi
  rw [addWitness_apply, addFun_block x y z q d hq hd0 hd8]

theorem addWitness_zero (x y z : ℤ) : addWitness x y z 0 = x := by
  rw [addWitness_coord x y z 0 0 0 (by omega) (by omega) (by omega) (by omega),
    addEntry_val_zero]

theorem addWitness_one (x y z : ℤ) : addWitness x y z 1 = y := by
  rw [addWitness_coord x y z 0 1 1 (by omega) (by omega) (by omega) (by omega),
    addEntry_y x y z 0 (by omega)]

theorem addWitness_two (x y z : ℤ) : addWitness x y z 2 = z := by
  rw [addWitness_coord x y z 0 2 2 (by omega) (by omega) (by omega) (by omega),
    addEntry_z x y z 0 (by omega)]

theorem addWitness_three (x y z : ℤ) : addWitness x y z 3 = 0 := by
  rw [addWitness_coord x y z 0 3 3 (by omega) (by omega) (by omega) (by omega),
    addEntry_c x y z 0 (by omega), addCount_zero]

theorem addWitness_four (x y z : ℤ) : addWitness x y z 4 = x := by
  rw [addWitness_coord x y z 0 4 4 (by omega) (by omega) (by omega) (by omega),
    addEntry_w x y z 0 (by omega), addCount_zero, add_zero]

theorem addWitness_eight (x y z : ℤ) : addWitness x y z 8 = y := by
  rw [addWitness_coord x y z 1 0 8 (by omega) (by omega) (by omega) (by omega),
    addEntry_val_one]

theorem addWitness_sixteen (x y z : ℤ) : addWitness x y z 16 = z := by
  rw [addWitness_coord x y z 2 0 16 (by omega) (by omega) (by omega) (by omega),
    addEntry_val_two]

theorem addWitness_trY (x y z r : ℤ) (hr0 : 0 ≤ r) (hrL : r ≤ (y.natAbs : ℤ)) :
    addWitness x y z (8 * r + 1) = y := by
  rw [addWitness_coord x y z r 1 (8 * r + 1) hr0 (by omega) (by omega) rfl,
    addEntry_y x y z r hrL]

theorem addWitness_trZ (x y z r : ℤ) (hr0 : 0 ≤ r) (hrL : r ≤ (y.natAbs : ℤ)) :
    addWitness x y z (8 * r + 2) = z := by
  rw [addWitness_coord x y z r 2 (8 * r + 2) hr0 (by omega) (by omega) rfl,
    addEntry_z x y z r hrL]

theorem addWitness_trC (x y z r : ℤ) (hr0 : 0 ≤ r) (hrL : r ≤ (y.natAbs : ℤ)) :
    addWitness x y z (8 * r + 3) = addCount y r := by
  rw [addWitness_coord x y z r 3 (8 * r + 3) hr0 (by omega) (by omega) rfl,
    addEntry_c x y z r hrL]

theorem addWitness_trW (x y z r : ℤ) (hr0 : 0 ≤ r) (hrL : r ≤ (y.natAbs : ℤ)) :
    addWitness x y z (8 * r + 4) = x + addCount y r := by
  rw [addWitness_coord x y z r 4 (8 * r + 4) hr0 (by omega) (by omega) rfl,
    addEntry_w x y z r hrL]

theorem addWitness_off (x y z r d : ℤ) (hr : r < 0 ∨ (y.natAbs : ℤ) < r) (hd : d ≠ 0)
    (hd0 : 0 ≤ d) (hd8 : d < 8) : addWitness x y z (8 * r + d) = 0 := by
  rcases hr with h | h
  · rw [addWitness_apply]
    exact addFun_block_neg x y z r d h hd8
  · rw [addWitness_coord x y z r d (8 * r + d) (by omega) hd0 hd8 rfl]
    exact addEntry_far x y z r d h hd

theorem addWitness_val (x y z i : ℤ) (h0 : i ≠ 0) (h1 : i ≠ 1) (h2 : i ≠ 2) :
    addWitness x y z (8 * i) = 0 := by
  rcases lt_or_le i 0 with h | h
  · rw [addWitness_apply]
    exact addFun_neg x y z (8 * i) (by omega)
  · rw [addWitness_coord x y z i 0 (8 * i) h (by omega) (by omega) (by omega),
      addEntry_val_other x y z i h0 h1 h2]

/-! ## 8.  The trace of a sum is a trace -/

theorem addWitness_mem_anchor (x y z : ℤ) : addWitness x y z ∈ addAnchor := by
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro i hi
    rw [addWitness_apply]
    exact addFun_neg x y z i hi
  · show addWitness x y z 3 = 0
    exact addWitness_three x y z
  · show addWitness x y z 4 = addWitness x y z 0
    rw [addWitness_four, addWitness_zero]
  · show addWitness x y z 8 = addWitness x y z 1
    rw [addWitness_eight, addWitness_one]
  · show addWitness x y z 16 = addWitness x y z 2
    rw [addWitness_sixteen, addWitness_two]

theorem addWitness_mem_transition (x y z : ℤ) (hxyz : z = x + y) :
    addWitness x y z ∈ transitionSet 8 addStep := by
  intro r
  rw [mem_addStep_window]
  rcases lt_or_le r 0 with hr | hr
  · refine Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩)
    · exact addWitness_off x y z r 1 (Or.inl hr) (by omega) (by omega) (by omega)
    · exact addWitness_off x y z r 2 (Or.inl hr) (by omega) (by omega) (by omega)
    · exact addWitness_off x y z r 3 (Or.inl hr) (by omega) (by omega) (by omega)
    · exact addWitness_off x y z r 4 (Or.inl hr) (by omega) (by omega) (by omega)
  · rcases lt_or_le ((y.natAbs : ℤ)) r with hfar | hnear
    · refine Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩)
      · exact addWitness_off x y z r 1 (Or.inr hfar) (by omega) (by omega) (by omega)
      · exact addWitness_off x y z r 2 (Or.inr hfar) (by omega) (by omega) (by omega)
      · exact addWitness_off x y z r 3 (Or.inr hfar) (by omega) (by omega) (by omega)
      · exact addWitness_off x y z r 4 (Or.inr hfar) (by omega) (by omega) (by omega)
    · rcases eq_or_lt_of_le hnear with heq | hlt
      · refine Or.inr (Or.inl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩)
        · show addWitness x y z (8 * r + 3) = addWitness x y z (8 * r + 1)
          rw [addWitness_trC x y z r hr hnear, addWitness_trY x y z r hr hnear, heq,
            addCount_len]
        · show addWitness x y z (8 * r + 4) = addWitness x y z (8 * r + 2)
          rw [addWitness_trW x y z r hr hnear, addWitness_trZ x y z r hr hnear, heq,
            addCount_len]
          omega
        · exact addWitness_off x y z (r + 1) 1 (Or.inr (by omega)) (by omega) (by omega)
            (by omega)
        · exact addWitness_off x y z (r + 1) 2 (Or.inr (by omega)) (by omega) (by omega)
            (by omega)
        · exact addWitness_off x y z (r + 1) 3 (Or.inr (by omega)) (by omega) (by omega)
            (by omega)
        · exact addWitness_off x y z (r + 1) 4 (Or.inr (by omega)) (by omega) (by omega)
            (by omega)
      · have hr1 : (0 : ℤ) ≤ r + 1 := by omega
        have hn1 : r + 1 ≤ (y.natAbs : ℤ) := by omega
        rcases le_or_lt 0 y with hy | hy
        · refine Or.inl (Or.inl ⟨?_, ?_, ?_, ?_⟩)
          · show addWitness x y z (8 * (r + 1) + 1) = addWitness x y z (8 * r + 1)
            rw [addWitness_trY x y z (r + 1) hr1 hn1, addWitness_trY x y z r hr hnear]
          · show addWitness x y z (8 * (r + 1) + 2) = addWitness x y z (8 * r + 2)
            rw [addWitness_trZ x y z (r + 1) hr1 hn1, addWitness_trZ x y z r hr hnear]
          · show addWitness x y z (8 * (r + 1) + 3) = addWitness x y z (8 * r + 3) + 1
            rw [addWitness_trC x y z (r + 1) hr1 hn1, addWitness_trC x y z r hr hnear,
              addCount_up y r hy]
          · show addWitness x y z (8 * (r + 1) + 4) = addWitness x y z (8 * r + 4) + 1
            rw [addWitness_trW x y z (r + 1) hr1 hn1, addWitness_trW x y z r hr hnear,
              addCount_up y r hy]
            ring
        · refine Or.inl (Or.inr ⟨?_, ?_, ?_, ?_⟩)
          · show addWitness x y z (8 * (r + 1) + 1) = addWitness x y z (8 * r + 1)
            rw [addWitness_trY x y z (r + 1) hr1 hn1, addWitness_trY x y z r hr hnear]
          · show addWitness x y z (8 * (r + 1) + 2) = addWitness x y z (8 * r + 2)
            rw [addWitness_trZ x y z (r + 1) hr1 hn1, addWitness_trZ x y z r hr hnear]
          · show addWitness x y z (8 * r + 3) = addWitness x y z (8 * (r + 1) + 3) + 1
            rw [addWitness_trC x y z (r + 1) hr1 hn1, addWitness_trC x y z r hr hnear]
            exact addCount_down y r hy
          · show addWitness x y z (8 * r + 4) = addWitness x y z (8 * (r + 1) + 4) + 1
            rw [addWitness_trW x y z (r + 1) hr1 hn1, addWitness_trW x y z r hr hnear,
              addCount_down y r hy]
            ring

/-! ## 9.  The identification -/

/-- **The projection of the traces, cut down to the window, is the graph of
addition.** -/
theorem addGraph_eq : addGraph = addProj ∩ windowSupport 3 := by
  have hc3 : ((3 : ℕ) : ℤ) = 3 := by norm_num
  ext f
  constructor
  · rintro ⟨hlo, hhi, heq⟩
    refine ⟨⟨addWitness (f 0) (f 1) (f 2), ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact addWitness_mem_transition (f 0) (f 1) (f 2) heq
    · exact addWitness_mem_anchor (f 0) (f 1) (f 2)
    · intro i
      rcases eq_or_ne i 0 with rfl | h0
      · rw [show (8 : ℤ) * 0 = 0 from by norm_num, addWitness_zero]
      · rcases eq_or_ne i 1 with rfl | h1
        · rw [show (8 : ℤ) * 1 = 8 from by norm_num, addWitness_eight]
        · rcases eq_or_ne i 2 with rfl | h2
          · rw [show (8 : ℤ) * 2 = 16 from by norm_num, addWitness_sixteen]
          · rw [addWitness_val (f 0) (f 1) (f 2) i h0 h1 h2]
            rcases lt_or_le i 0 with hneg | hpos
            · exact hlo i hneg
            · exact hhi i (by omega)
    · rw [mem_windowSupport_iff, hc3]
      exact ⟨hlo, hhi⟩
  · rintro ⟨⟨g, hg, hproj⟩, hw⟩
    rw [mem_windowSupport_iff, hc3] at hw
    have h := addTrace_eq hg
    have e2 : (8 : ℤ) * 2 = 16 := by norm_num
    have e0 : (8 : ℤ) * 0 = 0 := by norm_num
    have e1 : (8 : ℤ) * 1 = 8 := by norm_num
    refine ⟨hw.1, hw.2, ?_⟩
    rw [hproj 2, hproj 0, hproj 1, e2, e0, e1]
    exact h

/-- **Addition is generated.**  This is Higman's Lemma 2.4 at its base case: one
run of the transition device, anchored at the origin, with the successor
relation as its step. -/
theorem higmanGenerated_addGraph (hEq : ∀ d₁ d₂ : ℤ, HigmanGenerated (eqCoord d₁ d₂))
    (hSucc : ∀ d₁ d₂ : ℤ, HigmanGenerated (succCoord d₁ d₂)) : HigmanGenerated addGraph := by
  rw [addGraph_eq]
  exact HigmanGenerated.inter (higmanGenerated_addProj hEq hSucc)
    (higmanGenerated_windowSupport 3)

end Seq
end Higman
end GroupApproximation
