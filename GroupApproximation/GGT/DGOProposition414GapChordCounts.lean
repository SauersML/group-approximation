import GroupApproximation.GGT.DGOProposition414GapArcPartition

/-!
# Chord-length accounting for balanced gap children

The chord endpoints of consecutive gap children follow the greedy partner
list.  Before the one-edge orientation trims, their total length is exactly
the traversal cost of that list with both chord endpoints adjoined.  Each
trim changes each endpoint by at most one, giving the uniform correction used
in the aggregate side-count estimate of DGO Proposition 4.14.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

/-- Successive chord-walk segments have the traversal cost of the partner
list with its two boundary vertices. -/
theorem sum_chordWalk_dist (xs : List ℕ) (initial terminal : ℕ) :
    (∑ j : Fin (xs.length + 1),
      Nat.dist (chordWalkStart terminal xs j)
        (chordWalkFinish initial xs j)) =
      chordTraversalCost (initial :: xs ++ [terminal]) := by
  induction xs generalizing initial with
  | nil =>
      simp [Fin.sum_univ_one, chordWalkStart, chordWalkFinish,
        chordTraversalCost, Nat.dist_comm]
  | cons x xs ih =>
      rw [Fin.sum_univ_succ]
      have htail :
          (∑ j : Fin (xs.length + 1),
            Nat.dist (chordWalkStart terminal (x :: xs) j.succ)
              (chordWalkFinish initial (x :: xs) j.succ)) =
          ∑ j : Fin (xs.length + 1),
            Nat.dist (chordWalkStart terminal xs j)
              (chordWalkFinish x xs j) := by
        apply Finset.sum_congr rfl
        intro j _hj
        simp [chordWalkStart, chordWalkFinish]
      rw [htail, ih x]
      simp [chordWalkStart, chordWalkFinish, chordTraversalCost,
        Nat.dist_comm]

/-- Moving either endpoint of every chord-walk segment forward by at most one
adds at most two per segment to the total traversal. -/
theorem sum_orientedTrimmedChordWalk_dist_le
    (xs : List ℕ) (initial terminal : ℕ)
    (forward : Fin (xs.length + 1) → Prop) :
    (∑ j : Fin (xs.length + 1),
      Nat.dist
        (if h : j.val < xs.length then
          endpointByOrientation (forward j) (xs[j.val] + 1) xs[j.val]
        else terminal)
        (if h : 0 < j.val then
          endpointByOrientation (forward j) xs[j.val - 1]'(by omega)
            (xs[j.val - 1]'(by omega) + 1)
        else initial)) ≤
      chordTraversalCost (initial :: xs ++ [terminal]) +
        2 * (xs.length + 1) := by
  classical
  calc
    (∑ j : Fin (xs.length + 1),
      Nat.dist
        (if h : j.val < xs.length then
          endpointByOrientation (forward j) (xs[j.val] + 1) xs[j.val]
        else terminal)
        (if h : 0 < j.val then
          endpointByOrientation (forward j) xs[j.val - 1]'(by omega)
            (xs[j.val - 1]'(by omega) + 1)
        else initial)) ≤
      ∑ j : Fin (xs.length + 1),
        (Nat.dist (chordWalkStart terminal xs j)
          (chordWalkFinish initial xs j) + 2) := by
            apply Finset.sum_le_sum
            intro j _hj
            by_cases hf : forward j
            · by_cases hn : j.val < xs.length
              · by_cases hp : 0 < j.val
                · simp [endpointByOrientation, hf, hn, hp, chordWalkStart, chordWalkFinish,
                    Nat.dist]
                  omega
                · simp [endpointByOrientation, hf, hn, hp, chordWalkStart, chordWalkFinish,
                    Nat.dist]
                  omega
              · by_cases hp : 0 < j.val
                · simp [endpointByOrientation, hf, hn, hp, chordWalkStart, chordWalkFinish,
                    Nat.dist]
                  omega
                · simp [endpointByOrientation, hf, hn, hp, chordWalkStart, chordWalkFinish,
                    Nat.dist]
                  omega
            · by_cases hn : j.val < xs.length
              · by_cases hp : 0 < j.val
                · simp [endpointByOrientation, hf, hn, hp, chordWalkStart, chordWalkFinish,
                    Nat.dist]
                  omega
                · simp [endpointByOrientation, hf, hn, hp, chordWalkStart, chordWalkFinish,
                    Nat.dist]
                  omega
              · by_cases hp : 0 < j.val
                · simp [endpointByOrientation, hf, hn, hp, chordWalkStart, chordWalkFinish,
                    Nat.dist]
                  omega
                · simp [endpointByOrientation, hf, hn, hp, chordWalkStart, chordWalkFinish,
                    Nat.dist]
                  omega
    _ = chordTraversalCost (initial :: xs ++ [terminal]) +
        2 * (xs.length + 1) := by
      rw [Finset.sum_add_distrib, sum_chordWalk_dist]
      simp

/-- The orientation correction vanishes for an empty partner list and is at
most four times the number of partners otherwise. -/
theorem sum_orientedTrimmedChordWalk_dist_le_four_length
    (xs : List ℕ) (initial terminal : ℕ)
    (forward : Fin (xs.length + 1) → Prop) :
    (∑ j : Fin (xs.length + 1),
      Nat.dist
        (if h : j.val < xs.length then
          endpointByOrientation (forward j) (xs[j.val] + 1) xs[j.val]
        else terminal)
        (if h : 0 < j.val then
          endpointByOrientation (forward j) xs[j.val - 1]'(by omega)
            (xs[j.val - 1]'(by omega) + 1)
        else initial)) ≤
      chordTraversalCost (initial :: xs ++ [terminal]) + 4 * xs.length := by
  cases xs with
  | nil =>
      simp [Fin.sum_univ_one, chordTraversalCost, Nat.dist_comm]
  | cons x xs =>
      have h := sum_orientedTrimmedChordWalk_dist_le
        (x :: xs) initial terminal forward
      simp only [List.length_cons] at h ⊢
      omega

/-- Appending one boundary vertex in `[0,L]` costs at most `L`. -/
theorem chordTraversalCost_append_bounded_endpoint_le
    {xs : List ℕ} {terminal L : ℕ} (ht : terminal ≤ L)
    (hxs : ∀ x ∈ xs, x ≤ L) :
    chordTraversalCost (xs ++ [terminal]) ≤ chordTraversalCost xs + L := by
  induction xs with
  | nil => simp [chordTraversalCost]
  | cons x xs ih =>
      cases xs with
      | nil =>
          have hx : x ≤ L := hxs x (by simp)
          simp only [List.cons_append, List.nil_append, chordTraversalCost]
          unfold Nat.dist
          omega
      | cons y ys =>
          have htail : ∀ z ∈ y :: ys, z ≤ L := by
            intro z hz
            exact hxs z (by simp [hz])
          have hih := ih htail
          simpa only [List.cons_append, chordTraversalCost, Nat.add_assoc] using
            Nat.add_le_add_left hih (Nat.dist x y)

/-- Any partner traversal with both boundary vertices in `[0,L]` costs at
most its interior traversal plus `2L`. -/
theorem chordTraversalCost_with_two_endpoints_le
    {xs : List ℕ} {initial terminal L : ℕ}
    (hi : initial ≤ L) (ht : terminal ≤ L)
    (hxs : ∀ x ∈ xs, x ≤ L) :
    chordTraversalCost (initial :: xs ++ [terminal]) ≤
      chordTraversalCost xs + 2 * L := by
  cases xs with
  | nil =>
      simp only [List.nil_append, List.cons_append, chordTraversalCost]
      unfold Nat.dist
      omega
  | cons x xs =>
      have hx : x ≤ L := hxs x (by simp)
      have htail : ∀ y ∈ x :: xs, y ≤ L := by
        intro y hy
        exact hxs y hy
      have happ := chordTraversalCost_append_bounded_endpoint_le ht htail
      change Nat.dist initial x +
          chordTraversalCost ((x :: xs) ++ [terminal]) ≤
        chordTraversalCost (x :: xs) + 2 * L
      have hdist : Nat.dist initial x ≤ L := by
        unfold Nat.dist
        omega
      omega

end DGOProposition414
end GGT
end GroupApproximation
