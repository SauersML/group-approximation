import GroupApproximation.Sofic.MatchingPositions

/-!
# A run between two blocks has no gap

`MatchingPositions` says what two matched pairs do to each other — equal,
disjoint, or nested, never straddling.  That is local.  A curvature count needs
one global-ish fact about *blocks*: how the pairs joining one block to another
are arranged along the word.  This file proves they are arranged in the simplest
possible way.

## The statement

`Pp` and `Qp` mark the positions of two blocks, and the only things assumed of
them are that each is an **interval** of positions, that they are disjoint, and
that no matched pair has both ends in the same one.  Then, given two pairs each
joining `Pp` to `Qp`:

* `run_no_gap` — every letter strictly between their two `Pp`-ends is itself
  matched into `Qp`;
* `run_no_gap_snd` — every letter strictly between their two `Qp`-ends is itself
  matched back into `Pp`.

So the pairs joining one block to another are consecutive on both sides: **two
blocks meet in exactly one maximal run.**

The proof is three lines of geometry and the rest `omega`.  The two pairs are
forced to nest, `i < k < l < j`, because a disjoint configuration would put a
`Qp` position inside the `Pp` interval or the reverse.  A letter `m` between the
two `Pp`-ends must then be matched either back inside `(i, k)` — which is inside
the `Pp` interval, so a self-pair, excluded — or out past `l`, which is inside
the `Qp` interval.  There is nowhere else to go, and that is the whole content.

`pairIdx_covers` is the missing half of `MatchingPositions`'s matching lemmas: it
records uniqueness (`eq_of_fst_eq`, `eq_of_snd_eq`, `fst_ne_snd`) but not
existence, and a gap argument has to *name* the pair at a given letter.

## What this is for, and what it is not

Read with `Pp` the positions of a relator block and `Qp` the positions of the
boundary block, `run_no_gap_snd` says the boundary letters matched to that
relator form one contiguous stretch of `w` — the contiguity half of
`CurvatureAssembly.ShellGate`.  Stems cannot interrupt it: any position between
two relator positions carries that relator, and any position between two
boundary positions carries the boundary, so a `conj`/`stem` letter has nowhere
to sit inside either run.

**This does not prove a degree bound, and nothing here counts anything.**  "Some
relator block has at most three interior runs" is a statement about all blocks at
once; neither `DTree`'s shape nor `pairIdx` carries a counting invariant, and
supplying one is a separate obligation.  Nothing here discharges `ShellGate`,
`ShellDecomposition`, `GreendlingerConclusionSharp` or any gate.

Unconditional: no small cancellation, no minimality, no relators.  The blocks
enter only as two interval predicates on positions.
-/

namespace GroupApproximation
namespace SmallCancellationRouter
namespace DTree

universe u

variable {β : Type u}

/-! ## Every position is matched -/

/-- **The matching is perfect, positionally.**  Every position of the word is an
endpoint of exactly one pair; `MatchingPositions` records the uniqueness
(`eq_of_fst_eq`, `eq_of_snd_eq`, `fst_ne_snd`) and this is the existence.

Without it a count can say what two pairs do to each other but cannot name the
pair at a given letter, which is exactly what a gap argument has to do. -/
theorem pairIdx_covers :
    ∀ (T : DTree β) (m : ℕ), m < T.word.length →
      (∃ n : ℕ, (m, n) ∈ T.pairIdx) ∨ (∃ n : ℕ, (n, m) ∈ T.pairIdx) := by
  intro T
  induction T with
  | nil =>
      intro m hm
      rw [word_nil, List.length_nil] at hm
      omega
  | wrap a b A B ihA ihB =>
      intro m hm
      have hlen : (wrap a b A B).word.length
          = A.word.length + B.word.length + 2 := by
        rw [word_wrap, List.length_cons, List.length_append, List.length_cons]
        omega
      rw [hlen] at hm
      rcases Nat.lt_or_ge m 1 with h1 | h1
      · have hm0 : m = 0 := by omega
        subst hm0
        exact Or.inl ⟨A.word.length + 1, mem_pairIdx_root a b A B⟩
      · rcases Nat.lt_or_ge m (A.word.length + 1) with h2 | h2
        · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
          rcases ihA m' (by omega) with ⟨n, hn⟩ | ⟨n, hn⟩
          · exact Or.inl ⟨n + 1, mem_pairIdx_left hn⟩
          · exact Or.inr ⟨n + 1, mem_pairIdx_left hn⟩
        · rcases Nat.lt_or_ge m (A.word.length + 2) with h3 | h3
          · have hm1 : m = A.word.length + 1 := by omega
            subst hm1
            exact Or.inr ⟨0, mem_pairIdx_root a b A B⟩
          · obtain ⟨m', rfl⟩ : ∃ m', m = m' + (A.word.length + 2) :=
              ⟨m - (A.word.length + 2), by omega⟩
            rcases ihB m' (by omega) with ⟨n, hn⟩ | ⟨n, hn⟩
            · exact Or.inl ⟨n + (A.word.length + 2), mem_pairIdx_right hn⟩
            · exact Or.inr ⟨n + (A.word.length + 2), mem_pairIdx_right hn⟩

/-! ## A run between two blocks has no gap -/

/-- **No gap in a run, read at the opening side.**

`Pp` and `Qp` mark the positions of two *disjoint intervals* of the word — two
blocks — and no pair has both ends in `Pp`.  Given two pairs that each join `Pp`
to `Qp`, every letter between their two `Pp`-ends is itself matched into `Qp`.

So the pairs joining one block to another cannot be interrupted: they are
consecutive on both sides, and there is exactly one maximal run between any two
blocks.  Three inputs and no more: the interval property, the exclusion of
self-pairs, and `pairIdx_noncrossing`. -/
theorem run_no_gap {T : DTree β} {Pp Qp : ℕ → Prop}
    (hPint : ∀ {x y z : ℕ}, Pp x → Pp z → x < y → y < z → Pp y)
    (hQint : ∀ {x y z : ℕ}, Qp x → Qp z → x < y → y < z → Qp y)
    (hPQ : ∀ {x : ℕ}, Pp x → Qp x → False)
    (hnoPP : ∀ {x y : ℕ}, (x, y) ∈ T.pairIdx → Pp x → Pp y → False)
    {i j k l m : ℕ}
    (hij : (i, j) ∈ T.pairIdx) (hkl : (k, l) ∈ T.pairIdx)
    (hPi : Pp i) (hQj : Qp j) (hPk : Pp k) (hQl : Qp l)
    (him : i < m) (hmk : m < k) :
    ∃ n : ℕ, (m, n) ∈ T.pairIdx ∧ Pp m ∧ Qp n := by
  have hbij := lt_of_mem_pairIdx hij
  have hbkl := lt_of_mem_pairIdx hkl
  have hnest : i < k ∧ l < j := by
    rcases pairIdx_noncrossing T i j k l hij hkl with h | h | h | h | h
    · obtain ⟨h1, -⟩ := h
      omega
    · exact (hPQ (hPint hPi hPk (by omega) (by omega)) hQj).elim
    · exact (hPQ hPi (hQint hQl hQj (by omega) (by omega))).elim
    · exact h
    · obtain ⟨h1, -⟩ := h
      omega
  have hPm : Pp m := hPint hPi hPk him hmk
  rcases pairIdx_covers T m (by omega) with ⟨y, hxy⟩ | ⟨x, hxy⟩
  · have hbxy := lt_of_mem_pairIdx hxy
    obtain ⟨hiy, hyj⟩ := inside_of_fst_inside hij hxy him (by omega)
    rcases pairIdx_noncrossing T m y k l hxy hkl with h | h | h | h | h
    · obtain ⟨h1, -⟩ := h
      omega
    · exact (hnoPP hxy hPm (hPint hPi hPk hiy (by omega))).elim
    · omega
    · exact ⟨y, hxy, hPm, hQint hQl hQj h.2 hyj⟩
    · obtain ⟨h1, -⟩ := h
      omega
  · have hbxy := lt_of_mem_pairIdx hxy
    obtain ⟨hix, hxj⟩ := inside_of_snd_inside hij hxy (by omega) (by omega)
    exact (hnoPP hxy (hPint hPi hPk hix (by omega)) hPm).elim

/-- **No gap in a run, read at the closing side.**  The mirror of `run_no_gap`:
every letter between the two `Qp`-ends of two `Pp`–`Qp` pairs is itself matched
back into `Pp`.

This is the half a contiguity statement about the *boundary* block consumes,
since the boundary block is the `Qp` side. -/
theorem run_no_gap_snd {T : DTree β} {Pp Qp : ℕ → Prop}
    (hPint : ∀ {x y z : ℕ}, Pp x → Pp z → x < y → y < z → Pp y)
    (hQint : ∀ {x y z : ℕ}, Qp x → Qp z → x < y → y < z → Qp y)
    (hPQ : ∀ {x : ℕ}, Pp x → Qp x → False)
    (hnoQQ : ∀ {x y : ℕ}, (x, y) ∈ T.pairIdx → Qp x → Qp y → False)
    {i j k l m : ℕ}
    (hij : (i, j) ∈ T.pairIdx) (hkl : (k, l) ∈ T.pairIdx)
    (hPi : Pp i) (hQj : Qp j) (hPk : Pp k) (hQl : Qp l)
    (hlm : l < m) (hmj : m < j) :
    ∃ n : ℕ, (n, m) ∈ T.pairIdx ∧ Qp m ∧ Pp n := by
  have hbij := lt_of_mem_pairIdx hij
  have hbkl := lt_of_mem_pairIdx hkl
  have hnest : i < k ∧ l < j := by
    rcases pairIdx_noncrossing T i j k l hij hkl with h | h | h | h | h
    · obtain ⟨-, h2⟩ := h
      omega
    · exact (hPQ (hPint hPi hPk (by omega) (by omega)) hQj).elim
    · exact (hPQ hPi (hQint hQl hQj (by omega) (by omega))).elim
    · exact h
    · obtain ⟨-, h2⟩ := h
      omega
  have hQm : Qp m := hQint hQl hQj hlm hmj
  rcases pairIdx_covers T m (by omega) with ⟨y, hxy⟩ | ⟨x, hxy⟩
  · have hbxy := lt_of_mem_pairIdx hxy
    obtain ⟨hiy, hyj⟩ := inside_of_fst_inside hij hxy (by omega) hmj
    exact (hnoQQ hxy hQm (hQint hQl hQj (by omega) hyj)).elim
  · have hbxy := lt_of_mem_pairIdx hxy
    obtain ⟨hix, hxj⟩ := inside_of_snd_inside hij hxy (by omega) hmj
    rcases pairIdx_noncrossing T x m k l hxy hkl with h | h | h | h | h
    · obtain ⟨-, h2⟩ := h
      omega
    · omega
    · exact (hnoQQ hxy (hQint hQl hQj h hxj) hQm).elim
    · exact ⟨x, hxy, hQm, hPint hPi hPk hix h.1⟩
    · obtain ⟨-, h2⟩ := h
      omega

end DTree
end SmallCancellationRouter
end GroupApproximation
