import GroupApproximation.Higman.EnumeratedRange

/-!
# The trace format, its anchor, and the arithmetic it still asks for

`Higman.EnumeratedRangeGenerated` is the residue of Higman's Theorem 3, and the
route to it runs a computation along the index line.  This module fixes the
format of that computation, packages its global constraints as one generated
set, and isolates the arithmetic the transition relation still needs as a single
input, `Higman.BoundedWindowRE`.

## The format

Blocks of width four, so `θ²` reads the first track (`2² = 4`).  Block `i`
occupies the coordinates `4i` to `4i+3` and carries

* `4i`   --- the **value** `v`, which is the track the projection reads;
* `4i+1` --- the **counter** `j`;
* `4i+2` --- the **parameter** `p`, equal to `r+1` on the window of the `r`-th
  member of the enumeration and to `0` off it, so that `p ≠ 0` says "active";
* `4i+3` --- the **marker** `μ`, equal to `1` exactly when the block is active
  and its counter reads `0`.

## Why the marker is the counter's zero, and not the window's left end

The obvious marker is the left end of a window, and it is the wrong one.
`Seq.trackOffZero` forces a track to vanish off the *origin*, so a left-end
marker pinned at block `0` forces every window to start at block `0`, and only
sequences supported in `[0, ∞)` can be reached.

Marking instead the block where the counter reads zero repairs this.  Normalize
the enumeration so that every window contains the index `0` --- take the window
of `g_r` to be `[min 0 (least index), max 0 (greatest index)]`, which still
contains the support and is still computable.  Then the counter of *any* window
starts at or below `0` and ends at or above `0`, and since it increments by one
across the window it reads `0` at exactly one block of it
(`Seq.exists_counter_zero`).  Markers therefore biject with windows, so pinning
the marker to `1` at block `0` and to `0` everywhere else
(`Seq.anchorSet`) says exactly: there is one window, it contains block `0`, and
its counter reads `0` there.  With the counter incrementing, that gives
`j i = i` on the whole window (`Seq.counter_eq_index`), which is what puts the
value track at the right absolute position.

## What is left

`Seq.higmanGenerated_of_traceProjection` is the entry point: supply a generated
relation `A` between adjacent blocks and prove that the projection of the
anchored traces is the target.  The relation is a recursively enumerable
relation of bounded arity --- eight integers, one pair of blocks --- and that is
`Higman.BoundedWindowRE` below, the arithmetic of Higman's Section 2.  Nothing
here inhabits it.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

/-! ## 1.  Sequences supported in a window -/

/-- The sequences supported in the window `[0, n)`. -/
def windowSupport (n : ℕ) : Set E := vanishBelow 0 ∩ vanishAbove ((n : ℤ) - 1)

theorem mem_windowSupport_iff (n : ℕ) (f : E) :
    f ∈ windowSupport n ↔
      (∀ i : ℤ, i < 0 → f i = 0) ∧ ∀ i : ℤ, (n : ℤ) ≤ i → f i = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    have h2' : ∀ i : ℤ, (n : ℤ) - 1 < i → f i = 0 := h2
    exact ⟨h1, fun i hi => h2' i (by omega)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro i hi
    exact h2 i (by omega)

theorem higmanGenerated_windowSupport (n : ℕ) : HigmanGenerated (windowSupport n) :=
  higmanGenerated_window 0 ((n : ℤ) - 1)

/-! ## 2.  The counter calculus

A counter track that increments by one across an interval is an affine function
of the block index.  These three facts are everything the anchor argument needs,
and none of them mentions the sequence space. -/

/-- A track incrementing by one across `[a, b]` is determined by its left
value. -/
theorem counter_linear {j : ℤ → ℤ} {a b : ℤ}
    (hstep : ∀ i : ℤ, a ≤ i → i < b → j (i + 1) = j i + 1) :
    ∀ i : ℤ, a ≤ i → i ≤ b → j i = j a + (i - a) := by
  intro i hai
  induction i, hai using Int.leInduction with
  | base =>
      intro _
      simp
  | succ n hn ih =>
      intro hnb
      rw [hstep n hn (by omega), ih (by omega)]
      ring

/-- **With the anchor, the counter reads the block index.**  This is what puts
the value track at the right absolute position. -/
theorem counter_eq_index {j : ℤ → ℤ} {a b : ℤ} (ha : a ≤ 0) (hb : 0 ≤ b)
    (hstep : ∀ i : ℤ, a ≤ i → i < b → j (i + 1) = j i + 1) (h0 : j 0 = 0) :
    ∀ i : ℤ, a ≤ i → i ≤ b → j i = i := by
  have hlin := counter_linear hstep
  have hz := hlin 0 ha hb
  intro i hai hib
  have hi := hlin i hai hib
  omega

/-- **Every window carries exactly one block whose counter reads zero.**  The
normalization `lo r ≤ 0 ≤ hi r` is what makes the marker track count windows. -/
theorem exists_counter_zero {j : ℤ → ℤ} {a b : ℤ} (hab : a ≤ b)
    (hstep : ∀ i : ℤ, a ≤ i → i < b → j (i + 1) = j i + 1)
    (ha : j a ≤ 0) (hb : 0 ≤ j b) :
    ∃ i : ℤ, a ≤ i ∧ i ≤ b ∧ j i = 0 := by
  have hlin := counter_linear hstep
  have hjb : j b = j a + (b - a) := hlin b hab le_rfl
  have hge : a ≤ a - j a := by omega
  have hle : a - j a ≤ b := by omega
  refine ⟨a - j a, hge, hle, ?_⟩
  have hval := hlin (a - j a) hge hle
  omega

/-! ## 3.  The four tracks -/

/-- The value track of a trace in blocks of width four. -/
def trVal (g : E) (i : ℤ) : ℤ := g (4 * i)

/-- The counter track. -/
def trCnt (g : E) (i : ℤ) : ℤ := g (4 * i + 1)

/-- The parameter track; a block is *active* when it is nonzero. -/
def trPar (g : E) (i : ℤ) : ℤ := g (4 * i + 2)

/-- The marker track. -/
def trMrk (g : E) (i : ℤ) : ℤ := g (4 * i + 3)

/-! ## 4.  The anchor -/

/-- The global constraints on a trace: the marker reads `1` at the block of the
origin and `0` at every other block.  With the marker maintained as "active and
the counter reads zero", this says the trace has exactly one window, that the
window contains block `0`, and that its counter reads `0` there. -/
def anchorSet : Set E := pinAt 3 1 ∩ trackOffZero 4 3

theorem trMrk_zero_of_mem_anchorSet {g : E} (hg : g ∈ anchorSet) : trMrk g 0 = 1 := by
  have h : g 3 = 1 := hg.1
  show g (4 * 0 + 3) = 1
  simpa using h

theorem trMrk_off_zero_of_mem_anchorSet {g : E} (hg : g ∈ anchorSet) :
    ∀ i : ℤ, i ≠ 0 → trMrk g i = 0 := by
  intro i hi
  have h := hg.2 i hi
  show g (4 * i + 3) = 0
  simpa using h

theorem higmanGenerated_anchorSet : HigmanGenerated anchorSet :=
  HigmanGenerated.inter (higmanGenerated_pinAt 3 1)
    (higmanGenerated_trackOffZero 4 3 (by norm_num) (by norm_num))

/-! ## 5.  The entry point -/

/-- **The trace construction, specialized to the format above.**  Supply a
generated relation `A` between adjacent blocks and the identification of the
projection, and the target is generated.  The block width is four and the
projection is `θ²`, which reads the value track. -/
theorem higmanGenerated_of_traceProjection {A C : Set E} (hA : HigmanGenerated A)
    (hproj : ∀ f : E,
      (∃ g ∈ transitionSet 4 A ∩ anchorSet, ∀ i : ℤ, f i = g (4 * i)) ↔ f ∈ C) :
    HigmanGenerated C := by
  refine higmanGenerated_of_transitionProjection (t := 2) (k := 4) (by norm_num) hA
    higmanGenerated_anchorSet ?_
  intro f
  rw [show ((2 : ℤ) ^ (2 : ℕ)) = 4 from by norm_num]
  exact hproj f

end Seq

/-! ## 6.  The arithmetic that is left -/

/-- **Input: the arithmetic of Higman's Section 2.**  Every recursively
enumerable set of sequences supported in a fixed finite window is generated.

This is what the transition relation of a trace asks for, at the single arity
eight --- one pair of blocks of width four.  It is the part of Section 2 that
precedes Lemma 2.8, and it is not reachable from the lattice and position
calculus alone: the operations generate only agreement and support conditions
until `ωₘ` is used, so every step of it runs through the transition device
again, on a simpler relation.

**Nothing inhabits this structure.** -/
structure BoundedWindowRE where
  /-- Recursively enumerable sets of window-supported sequences are generated. -/
  generated : ∀ (n : ℕ) (B : Set Seq.E), REset B → B ⊆ Seq.windowSupport n →
    Seq.HigmanGenerated B

end Higman
end GroupApproximation
