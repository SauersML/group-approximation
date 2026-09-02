import GroupApproximation.GGT.DGOProposition414GapSurvivors

/-!
# Ordered gap partitions for DGO Proposition 4.14

The broken components in one balanced half are listed in their arc order.
Removing their side coordinates cuts the ambient side interval into one more
gap than there are broken components.  This file proves the abstract finite
telescoping and coverage statements used by the child-side counts and by the
owner assignment for surviving components.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

/-- Initial coordinate of the `j`-th gap determined by `xs`. -/
def orderedGapStart (lo : ℕ) (xs : List ℕ) : ℕ → ℕ
  | 0 => lo
  | j + 1 => (xs[j]?).getD lo + 1

/-- Terminal coordinate of the `j`-th gap determined by `xs`. -/
def orderedGapFinish (hi : ℕ) (xs : List ℕ) (j : ℕ) : ℕ :=
  (xs[j]?).getD hi

@[simp]
theorem orderedGapStart_zero (lo : ℕ) (xs : List ℕ) :
    orderedGapStart lo xs 0 = lo := by
  rfl

@[simp]
theorem orderedGapFinish_nil (hi j : ℕ) :
    orderedGapFinish hi [] j = hi := by
  simp [orderedGapFinish]

@[simp]
theorem orderedGapFinish_cons_zero (hi x : ℕ) (xs : List ℕ) :
    orderedGapFinish hi (x :: xs) 0 = x := by
  simp [orderedGapFinish]

@[simp]
theorem orderedGapFinish_cons_succ (hi x : ℕ) (xs : List ℕ) (j : ℕ) :
    orderedGapFinish hi (x :: xs) (j + 1) =
      orderedGapFinish hi xs j := by
  simp [orderedGapFinish]

theorem orderedGapStart_cons_succ (lo x : ℕ) (xs : List ℕ) (j : ℕ)
    (hj : j < xs.length + 1) :
    orderedGapStart lo (x :: xs) (j + 1) =
      orderedGapStart (x + 1) xs j := by
  cases j with
  | zero => simp [orderedGapStart]
  | succ j =>
      have hjx : j < xs.length := by omega
      simp [orderedGapStart, hjx]

/-- The ordered gaps omit exactly the listed singleton coordinates. -/
theorem sum_orderedGap_width_add_length (lo hi : ℕ) (xs : List ℕ)
    (hlo : ∀ x ∈ xs, lo ≤ x)
    (hhi : ∀ x ∈ xs, x < hi) (hordered : xs.Pairwise (fun x y => x < y)) :
    (∑ j : Fin (xs.length + 1),
        (orderedGapFinish hi xs j - orderedGapStart lo xs j)) +
      xs.length = hi - lo := by
  induction xs generalizing lo with
  | nil =>
      simp [orderedGapStart, orderedGapFinish]
  | cons x xs ih =>
      have hlox : lo ≤ x := hlo x (by simp)
      have hxhi : x < hi := hhi x (by simp)
      have htailOrdered : xs.Pairwise (fun y z => y < z) := hordered.tail
      have htailLo : ∀ y ∈ xs, x + 1 ≤ y := by
        intro y hy
        have hxy : x < y := (List.pairwise_cons.mp hordered).1 y hy
        omega
      have htailHi : ∀ y ∈ xs, y < hi := by
        intro y hy
        exact hhi y (by simp [hy])
      have htail := ih (x + 1) htailLo htailHi htailOrdered
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero]
      have hzero :
          orderedGapFinish hi (x :: xs) 0 -
              orderedGapStart lo (x :: xs) 0 = x - lo := by
        simp [orderedGapStart, orderedGapFinish]
      rw [hzero]
      have hsum :
          (∑ j : Fin (xs.length + 1),
              (orderedGapFinish hi (x :: xs) j.succ.val -
                orderedGapStart lo (x :: xs) j.succ.val)) =
            ∑ j : Fin (xs.length + 1),
              (orderedGapFinish hi xs j.val -
                orderedGapStart (x + 1) xs j.val) := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [show j.succ.val = j.val + 1 by rfl,
          orderedGapFinish_cons_succ,
          orderedGapStart_cons_succ lo x xs j.val j.isLt]
      calc
        (x - lo + ∑ j : Fin (xs.length + 1),
            (orderedGapFinish hi (x :: xs) j.succ.val -
              orderedGapStart lo (x :: xs) j.succ.val)) +
            (x :: xs).length =
          (x - lo + ∑ j : Fin (xs.length + 1),
            (orderedGapFinish hi xs j.val -
              orderedGapStart (x + 1) xs j.val)) +
            (x :: xs).length := congrArg
              (fun z => (x - lo + z) + (x :: xs).length) hsum
        _ = hi - lo := by
          simp only [List.length_cons]
          omega

/-- Every coordinate not listed in a strictly ordered finite set belongs to
one of its gaps. -/
theorem exists_orderedGap_of_not_mem (lo hi y : ℕ) (xs : List ℕ)
    (hloy : lo ≤ y) (hyhi : y < hi) (hnot : y ∉ xs)
    (hordered : xs.Pairwise (fun x z => x < z)) :
    ∃ j : Fin (xs.length + 1),
      orderedGapStart lo xs j.val ≤ y ∧
        y < orderedGapFinish hi xs j.val := by
  induction xs generalizing lo with
  | nil =>
      refine ⟨⟨0, by simp⟩, ?_⟩
      simpa [orderedGapStart, orderedGapFinish] using ⟨hloy, hyhi⟩
  | cons x xs ih =>
      have hyx : y < x ∨ x < y := by
        have hne : y ≠ x := by
          intro heq
          exact hnot (by simp [heq])
        omega
      rcases hyx with hyx | hxy
      · refine ⟨⟨0, by simp⟩, ?_⟩
        simpa [orderedGapStart, orderedGapFinish] using ⟨hloy, hyx⟩
      · have hx1y : x + 1 ≤ y := by omega
        have hnotTail : y ∉ xs := by
          intro hy
          exact hnot (by simp [hy])
        obtain ⟨j, hj⟩ := ih (x + 1) hx1y hnotTail hordered.tail
        refine ⟨⟨j.val + 1, by simp; omega⟩, ?_⟩
        rw [orderedGapFinish_cons_succ,
          orderedGapStart_cons_succ lo x xs j.val j.isLt]
        exact hj

end DGOProposition414
end GGT
end GroupApproximation
