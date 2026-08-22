import GroupApproximation.Higman.EnumeratedRangeTrace

/-!
# The transition relation of a trace, and the bridge to the track equations

`Higman.EnumeratedRangeTrace` fixes the trace format --- blocks of width four
carrying value, counter, parameter and marker --- and packages the global
constraints as `Seq.anchorSet`.  What is still between it and
`Higman.EnumeratedRangeGenerated` is the *local* constraint: a relation between
adjacent blocks, and the identification of its `θ²` projection with the range of
the enumeration.

This module supplies everything up to that identification.

## The window of a member, normalized

`Seq.loIdx` and `Seq.hiIdx` read the least and greatest index occurring in the
code `c r`, clamped to be at most and at least `0`.  The clamping is the design
correction the format rests on: every window then contains the index `0`, so
every window's counter crosses `0` exactly once, so the marker track counts
windows and `Seq.anchorSet` makes the window unique.  `Seq.gseq_eq_zero_of_lt`
and `Seq.gseq_eq_zero_of_gt` are the price of the clamping being harmless --- a
member vanishes outside its normalized window, so widening the window does not
change the value track.

## The bridge

`Seq.transitionSet 4 A` is stated in raw coordinates: it reads the eight
coordinates `4i` through `4i+7` as one window and asks that the window lie in
`A`.  `Seq.mem_transitionSet_blockPairSet` turns that into eight *track*
equations,

    f ∈ transitionSet 4 (blockPairSet P) ↔
      ∀ i, P (trVal f i) (trCnt f i) (trPar f i) (trMrk f i)
             (trVal f (i+1)) (trCnt f (i+1)) (trPar f (i+1)) (trMrk f (i+1)) ,

after which nothing downstream has to mention a coordinate again.  This is the
step that makes the correctness proof writable in the language of the format
rather than in the language of `windowAt`.

## The relation itself

`Seq.traceRel` is the concrete relation, in the four cases the format needs:
both blocks inactive, a window starting, a window stepping, a window ending.
`Seq.higmanGenerated_blockPairSet` shows that `Higman.BoundedWindowRE` --- the
arithmetic of Higman's Section 2, fanned out separately --- generates it, given
that it is recursively enumerable.

## What is left

Two things, both stated precisely at the end of this file.

* `REset (blockPairSet (traceRel c))` --- that the relation is recursively
  enumerable.  It is a computability statement about `c`, `loIdx`, `hiIdx` and
  `gseq`, of the same character as `Higman.BlockComputable`, and it is
  independent of everything else here.
* The projection identity, which `Seq.higmanGenerated_of_traceProjection`
  consumes.  Its two halves are the extraction of `r` from a trace and the
  explicit construction of the trace of each `r`.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

/-! ## 1.  The members of the enumeration and their normalized windows -/

/-- The `r`-th member of the enumeration. -/
noncomputable def gseq (c : ℕ → List (ℤ × ℤ)) (r : ℕ) : E := seqOfList (c r)

/-- The left end of the normalized window of the `r`-th member: the least index
occurring in its code, clamped to be at most `0`. -/
def loIdx (c : ℕ → List (ℤ × ℤ)) (r : ℕ) : ℤ := ((c r).map Prod.fst).foldr min 0

/-- The right end, clamped to be at least `0`. -/
def hiIdx (c : ℕ → List (ℤ × ℤ)) (r : ℕ) : ℤ := ((c r).map Prod.fst).foldr max 0

theorem foldr_min_le_zero (l : List ℤ) : l.foldr min 0 ≤ 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.foldr_cons]
      exact le_trans (min_le_right a _) ih

theorem zero_le_foldr_max (l : List ℤ) : 0 ≤ l.foldr max 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.foldr_cons]
      exact le_trans ih (le_max_right a _)

theorem foldr_min_le_of_mem : ∀ (l : List ℤ) {x : ℤ}, x ∈ l → l.foldr min 0 ≤ x := by
  intro l
  induction l with
  | nil =>
      intro x hx
      simp at hx
  | cons a t ih =>
      intro x hx
      rw [List.foldr_cons]
      rcases List.mem_cons.mp hx with h | h
      · rw [h]
        exact min_le_left _ _
      · exact le_trans (min_le_right _ _) (ih h)

theorem le_foldr_max_of_mem : ∀ (l : List ℤ) {x : ℤ}, x ∈ l → x ≤ l.foldr max 0 := by
  intro l
  induction l with
  | nil =>
      intro x hx
      simp at hx
  | cons a t ih =>
      intro x hx
      rw [List.foldr_cons]
      rcases List.mem_cons.mp hx with h | h
      · rw [h]
        exact le_max_left _ _
      · exact le_trans (ih h) (le_max_right _ _)

theorem loIdx_nonpos (c : ℕ → List (ℤ × ℤ)) (r : ℕ) : loIdx c r ≤ 0 :=
  foldr_min_le_zero _

theorem hiIdx_nonneg (c : ℕ → List (ℤ × ℤ)) (r : ℕ) : 0 ≤ hiIdx c r :=
  zero_le_foldr_max _

/-- A coded sequence vanishes at every index its code does not mention. -/
theorem seqOfList_apply_eq_zero (i : ℤ) :
    ∀ l : List (ℤ × ℤ), (∀ p ∈ l, p.1 ≠ i) → seqOfList l i = 0 := by
  intro l
  induction l with
  | nil =>
      intro _
      simp [seqOfList]
  | cons a t ih =>
      intro h
      have hne : a.1 ≠ i := h a (by simp)
      have ht : seqOfList t i = 0 := ih fun p hp => h p (List.mem_cons_of_mem _ hp)
      unfold seqOfList at ht ⊢
      rw [List.map_cons, List.sum_cons, Finsupp.add_apply, ht, add_zero,
        Finsupp.single_apply, if_neg hne]

theorem gseq_eq_zero_of_lt (c : ℕ → List (ℤ × ℤ)) (r : ℕ) {i : ℤ}
    (hi : i < loIdx c r) : gseq c r i = 0 := by
  refine seqOfList_apply_eq_zero i (c r) fun p hp => ?_
  have hle : loIdx c r ≤ p.1 :=
    foldr_min_le_of_mem _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
  omega

theorem gseq_eq_zero_of_gt (c : ℕ → List (ℤ × ℤ)) (r : ℕ) {i : ℤ}
    (hi : hiIdx c r < i) : gseq c r i = 0 := by
  refine seqOfList_apply_eq_zero i (c r) fun p hp => ?_
  have hle : p.1 ≤ hiIdx c r :=
    le_foldr_max_of_mem _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
  omega

/-! ## 2.  From raw coordinates to track equations -/

theorem windowAt_mem_windowSupport (m : ℕ) (s : ℤ) (f : E) :
    windowAt m s f ∈ windowSupport m := by
  refine ⟨?_, ?_⟩
  · intro j hj
    rw [windowAt_apply, if_neg (by simp only [Finset.mem_Ico]; omega)]
  · intro j hj
    rw [windowAt_apply, if_neg (by simp only [Finset.mem_Ico]; omega)]

theorem windowAt_eight_apply (i : ℤ) (f : E) {j : ℤ} (hj0 : 0 ≤ j) (hj8 : j < 8) :
    windowAt (2 * 4) (((4 : ℕ) : ℤ) * i) f j = f (4 * i + j) := by
  rw [windowAt_apply, if_pos (Finset.mem_Ico.mpr ⟨hj0, by omega⟩)]
  congr 1

theorem windowAt_eight_zero (f : E) (i : ℤ) :
    windowAt (2 * 4) (((4 : ℕ) : ℤ) * i) f 0 = trVal f i := by
  have h : windowAt (2 * 4) (((4 : ℕ) : ℤ) * i) f 0 = f (4 * i + 0) :=
    windowAt_eight_apply i f (by norm_num) (by norm_num)
  have harith : (4 : ℤ) * i + 0 = 4 * i := by ring
  rw [harith] at h
  exact h

theorem windowAt_eight_one (f : E) (i : ℤ) :
    windowAt (2 * 4) (((4 : ℕ) : ℤ) * i) f 1 = trCnt f i :=
  windowAt_eight_apply i f (by norm_num) (by norm_num)

theorem windowAt_eight_two (f : E) (i : ℤ) :
    windowAt (2 * 4) (((4 : ℕ) : ℤ) * i) f 2 = trPar f i :=
  windowAt_eight_apply i f (by norm_num) (by norm_num)

theorem windowAt_eight_three (f : E) (i : ℤ) :
    windowAt (2 * 4) (((4 : ℕ) : ℤ) * i) f 3 = trMrk f i :=
  windowAt_eight_apply i f (by norm_num) (by norm_num)

theorem windowAt_eight_four (f : E) (i : ℤ) :
    windowAt (2 * 4) (((4 : ℕ) : ℤ) * i) f 4 = trVal f (i + 1) := by
  have h : windowAt (2 * 4) (((4 : ℕ) : ℤ) * i) f 4 = f (4 * i + 4) :=
    windowAt_eight_apply i f (by norm_num) (by norm_num)
  have harith : (4 : ℤ) * i + 4 = 4 * (i + 1) := by ring
  rw [harith] at h
  exact h

theorem windowAt_eight_five (f : E) (i : ℤ) :
    windowAt (2 * 4) (((4 : ℕ) : ℤ) * i) f 5 = trCnt f (i + 1) := by
  have h : windowAt (2 * 4) (((4 : ℕ) : ℤ) * i) f 5 = f (4 * i + 5) :=
    windowAt_eight_apply i f (by norm_num) (by norm_num)
  have harith : (4 : ℤ) * i + 5 = 4 * (i + 1) + 1 := by ring
  rw [harith] at h
  exact h

theorem windowAt_eight_six (f : E) (i : ℤ) :
    windowAt (2 * 4) (((4 : ℕ) : ℤ) * i) f 6 = trPar f (i + 1) := by
  have h : windowAt (2 * 4) (((4 : ℕ) : ℤ) * i) f 6 = f (4 * i + 6) :=
    windowAt_eight_apply i f (by norm_num) (by norm_num)
  have harith : (4 : ℤ) * i + 6 = 4 * (i + 1) + 2 := by ring
  rw [harith] at h
  exact h

theorem windowAt_eight_seven (f : E) (i : ℤ) :
    windowAt (2 * 4) (((4 : ℕ) : ℤ) * i) f 7 = trMrk f (i + 1) := by
  have h : windowAt (2 * 4) (((4 : ℕ) : ℤ) * i) f 7 = f (4 * i + 7) :=
    windowAt_eight_apply i f (by norm_num) (by norm_num)
  have harith : (4 : ℤ) * i + 7 = 4 * (i + 1) + 3 := by ring
  rw [harith] at h
  exact h

/-- A relation between two adjacent blocks of width four, as a set of sequences
supported in the window `[0, 8)`. -/
def blockPairSet (P : ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → Prop) : Set E :=
  windowSupport 8 ∩ {w : E | P (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7)}

/-- Membership in `blockPairSet`, with the predicate in applied form.  The
set-builder binds its own variable, so a rewrite by the coordinate lemmas finds
nothing until membership has been unfolded to this shape. -/
theorem mem_blockPairSet_iff (P : ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → Prop) (w : E) :
    w ∈ blockPairSet P ↔
      w ∈ windowSupport 8 ∧
        P (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7) :=
  Iff.rfl

/-- **The bridge.**  A transition condition in raw coordinates is a condition on
the four tracks of adjacent blocks.  Nothing downstream of this has to mention a
coordinate. -/
theorem mem_transitionSet_blockPairSet
    (P : ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → Prop) (f : E) :
    f ∈ transitionSet 4 (blockPairSet P) ↔
      ∀ i : ℤ, P (trVal f i) (trCnt f i) (trPar f i) (trMrk f i)
        (trVal f (i + 1)) (trCnt f (i + 1)) (trPar f (i + 1)) (trMrk f (i + 1)) := by
  have key : ∀ i : ℤ,
      (windowAt (2 * 4) (((4 : ℕ) : ℤ) * i) f ∈ blockPairSet P ↔
        P (trVal f i) (trCnt f i) (trPar f i) (trMrk f i)
          (trVal f (i + 1)) (trCnt f (i + 1)) (trPar f (i + 1))
          (trMrk f (i + 1))) := by
    intro i
    rw [mem_blockPairSet_iff]
    constructor
    · rintro ⟨-, hP⟩
      rwa [windowAt_eight_zero, windowAt_eight_one, windowAt_eight_two,
        windowAt_eight_three, windowAt_eight_four, windowAt_eight_five,
        windowAt_eight_six, windowAt_eight_seven] at hP
    · intro hP
      refine ⟨windowAt_mem_windowSupport _ _ _, ?_⟩
      rwa [windowAt_eight_zero, windowAt_eight_one, windowAt_eight_two,
        windowAt_eight_three, windowAt_eight_four, windowAt_eight_five,
        windowAt_eight_six, windowAt_eight_seven]
  constructor
  · intro hf i
    exact (key i).mp (hf i)
  · intro hf i
    exact (key i).mpr (hf i)

/-- The arithmetic input generates any recursively enumerable block relation. -/
theorem higmanGenerated_blockPairSet (h : BoundedWindowRE)
    (P : ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → Prop) (hre : REset (blockPairSet P)) :
    HigmanGenerated (blockPairSet P) :=
  h.generated 8 (blockPairSet P) hre fun _ hw => hw.1

/-! ## 3.  The relation the format asks for -/

/-- The index recovered from a parameter value: an active block carries `r + 1`,
so that `0` is available to mean inactive. -/
def parIdx (p : ℤ) : ℕ := (p - 1).toNat

/-- The parameter track carries `r + 1`, so every clause that reads it back has
to recover `r`.  Five of the eleven clauses of `traceRel` need this. -/
theorem parIdx_natCast_add_one (r : ℕ) : parIdx ((r : ℤ) + 1) = r := by
  unfold parIdx
  omega

/-- **The transition relation of a trace.**  Four cases: both blocks inactive,
a window starting, a window stepping, a window ending.  The marker clause is a
condition on one block at a time, and says that the marker reads the counter's
zero --- which is what makes markers count windows. -/
def traceRel (c : ℕ → List (ℤ × ℤ)) (v j p m v' j' p' m' : ℤ) : Prop :=
  0 ≤ p ∧ 0 ≤ p' ∧
  m = (if 1 ≤ p ∧ j = 0 then 1 else 0) ∧
  m' = (if 1 ≤ p' ∧ j' = 0 then 1 else 0) ∧
  (p = 0 → v = 0 ∧ j = 0) ∧
  (p' = 0 → v' = 0 ∧ j' = 0) ∧
  (1 ≤ p → loIdx c (parIdx p) ≤ j ∧ j ≤ hiIdx c (parIdx p) ∧
    v = gseq c (parIdx p) j) ∧
  (1 ≤ p' → loIdx c (parIdx p') ≤ j' ∧ j' ≤ hiIdx c (parIdx p') ∧
    v' = gseq c (parIdx p') j') ∧
  (1 ≤ p → 1 ≤ p' → p' = p ∧ j' = j + 1) ∧
  (1 ≤ p → p' = 0 → j = hiIdx c (parIdx p)) ∧
  (p = 0 → 1 ≤ p' → j' = loIdx c (parIdx p'))

/-- The anchored traces of an enumeration. -/
def traceSet (c : ℕ → List (ℤ × ℤ)) : Set E :=
  transitionSet 4 (blockPairSet (traceRel c)) ∩ anchorSet

/-- **What the trace construction still owes.**  Given the arithmetic input and
the recursive enumerability of the relation, the range of the enumeration is
generated as soon as the projection of the anchored traces is identified with
it. -/
theorem higmanGenerated_range_of_projection (h : BoundedWindowRE)
    (c : ℕ → List (ℤ × ℤ)) (hre : REset (blockPairSet (traceRel c)))
    (hproj : ∀ f : E,
      (∃ g ∈ traceSet c, ∀ i : ℤ, f i = g (4 * i)) ↔
        f ∈ {g : E | ∃ r : ℕ, seqOfList (c r) = g}) :
    HigmanGenerated {g : E | ∃ r : ℕ, seqOfList (c r) = g} :=
  higmanGenerated_of_traceProjection (higmanGenerated_blockPairSet h (traceRel c) hre)
    hproj

end Seq
end Higman
end GroupApproximation
