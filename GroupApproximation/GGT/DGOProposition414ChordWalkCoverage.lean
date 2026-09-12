import GroupApproximation.GGT.DGOProposition414CrossHalfPartner

/-!
# Covering chord edges by the opposite-half walk

The chord intervals of a greedy half form a walk from one endpoint of the
global chord to the other through the (generally nonmonotone) partner list.
Every chord edge is therefore crossed by some interval.  Trimming a segment
endpoint across a selected partner edge can remove only that partner edge;
all chord edges absent from the partner list remain covered.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

/-- The unoriented interval with endpoints `a,b` contains the edge `[y,y+1]`. -/
def EdgeBetween (a b y : ℕ) : Prop :=
  (a ≤ y ∧ y + 1 ≤ b) ∨ (b ≤ y ∧ y + 1 ≤ a)

/-- The next vertex of the walk at segment `j`. -/
def chordWalkStart (terminal : ℕ) (xs : List ℕ)
    (j : Fin (xs.length + 1)) : ℕ :=
  if h : j.val < xs.length then xs[j.val] else terminal

/-- The preceding vertex of the walk at segment `j`. -/
def chordWalkFinish (initial : ℕ) (xs : List ℕ)
    (j : Fin (xs.length + 1)) : ℕ :=
  if h : 0 < j.val then xs[j.val - 1]'(by omega) else initial

/-- Any edge separating the endpoints of a finite walk occurs in one of its
successive unoriented segments.  No monotonicity of the intermediate vertices
is used. -/
theorem exists_edgeBetween_chordWalk
    (xs : List ℕ) (initial terminal y : ℕ)
    (houter : EdgeBetween initial terminal y) :
    ∃ j : Fin (xs.length + 1),
      EdgeBetween (chordWalkStart terminal xs j)
        (chordWalkFinish initial xs j) y := by
  induction xs generalizing initial with
  | nil =>
      refine ⟨⟨0, by simp⟩, ?_⟩
      simpa [chordWalkStart, chordWalkFinish, EdgeBetween] using houter.symm
  | cons x xs ih =>
      by_cases hfirst : EdgeBetween initial x y
      · refine ⟨⟨0, by simp⟩, ?_⟩
        unfold EdgeBetween at hfirst ⊢
        simp [chordWalkStart, chordWalkFinish]
        omega
      · have htail : EdgeBetween x terminal y := by
          unfold EdgeBetween at houter hfirst ⊢
          omega
        obtain ⟨j, hj⟩ := ih x htail
        rcases j with ⟨j, hjlt⟩
        cases j with
        | zero =>
            refine ⟨⟨1, by simp⟩, ?_⟩
            simpa [chordWalkStart, chordWalkFinish] using hj
        | succ j =>
            refine ⟨⟨j + 2, by simp; omega⟩, ?_⟩
            by_cases h : j + 1 < xs.length
            · have h' : j + 2 ≤ xs.length := by omega
              simpa [chordWalkStart, chordWalkFinish, h, h',
                List.getElem_cons_succ] using hj
            · have h' : ¬ j + 2 ≤ xs.length := by omega
              simpa [chordWalkStart, chordWalkFinish, h, h',
                List.getElem_cons_succ] using hj

/-- Moving the first endpoint one step forward preserves every covered edge
except the edge starting at that endpoint. -/
theorem edgeBetween_succ_left {a b y : ℕ}
    (h : EdgeBetween a b y) (hne : y ≠ a) :
    EdgeBetween (a + 1) b y := by
  unfold EdgeBetween at h ⊢
  omega

/-- Moving the second endpoint one step forward preserves every covered edge
except the edge starting at that endpoint. -/
theorem edgeBetween_succ_right {a b y : ℕ}
    (h : EdgeBetween a b y) (hne : y ≠ b) :
    EdgeBetween a (b + 1) y := by
  unfold EdgeBetween at h ⊢
  omega

/-- First-half trimming moves the next-partner endpoint across its own edge.
An edge not named by the partner list still occurs in some trimmed segment. -/
theorem exists_edgeBetween_firstTrimmedChordWalk
    (xs : List ℕ) (L y : ℕ) (hy : y < L) (hnot : y ∉ xs) :
    ∃ j : Fin (xs.length + 1),
      EdgeBetween
        (if h : j.val < xs.length then xs[j.val] + 1 else L)
        (chordWalkFinish 0 xs j) y := by
  obtain ⟨j, hj⟩ := exists_edgeBetween_chordWalk xs 0 L y
    (by simp [EdgeBetween, hy])
  refine ⟨j, ?_⟩
  by_cases h : j.val < xs.length
  · have hne : y ≠ xs[j.val] := by
      intro heq
      exact hnot (heq ▸ List.getElem_mem h)
    have hstart : chordWalkStart L xs j = xs[j.val] := by
      simp [chordWalkStart, h]
    rw [hstart] at hj
    simpa [h] using edgeBetween_succ_left hj hne
  · simpa [chordWalkStart, h] using hj

/-- Wrapped-half trimming moves the previous-partner endpoint across its own
edge.  Again, every edge absent from the partner list remains covered. -/
theorem exists_edgeBetween_secondTrimmedChordWalk
    (xs : List ℕ) (L y : ℕ) (hy : y < L) (hnot : y ∉ xs) :
    ∃ j : Fin (xs.length + 1),
      EdgeBetween (chordWalkStart 0 xs j)
        (if h : 0 < j.val then xs[j.val - 1]'(by omega) + 1 else L) y := by
  obtain ⟨j, hj⟩ := exists_edgeBetween_chordWalk xs L 0 y
    (by simp [EdgeBetween, hy])
  refine ⟨j, ?_⟩
  by_cases h : 0 < j.val
  · have hne : y ≠ xs[j.val - 1]'(by omega) := by
      intro heq
      exact hnot (heq ▸ List.getElem_mem (by omega))
    have hfinish : chordWalkFinish L xs j = xs[j.val - 1]'(by omega) := by
      simp [chordWalkFinish, h]
    rw [hfinish] at hj
    simpa [h] using edgeBetween_succ_right hj hne
  · simpa [chordWalkFinish, h] using hj

end DGOProposition414
end GGT
end GroupApproximation
