import GroupApproximation.Sofic.NonCrossingMatching

/-!
# The matching as positions, and non-crossing as an inequality

`NonCrossingMatching` records a matched pair as a pair of *values*,
`DTree.pairs : List (β × β)`.  A curvature count cannot run on values: it needs
to know which stretch of the word a pair brackets, which pairs lie inside that
stretch, and which letters two pairs separate.  All of that is positional, and
none of it is visible in `pairs`.

`DTree.pairIdx` is the same list read as positions in `DTree.word`.  It is
defined by the same recursion as `pairs`: in `wrap a b A B` the word is

```text
    a  ++  A.word  ++  b  ++  B.word
    0      1 … n            n+1        n+2 …           (n = A.word.length)
```

so the root pair sits at `(0, n + 1)`, the pairs of `A` shift by `1`, and the
pairs of `B` shift by `n + 2`.  That is the whole definition, and everything
below is a structural induction over it.

## What is here

* `exists_block_of_mem_pairIdx` — the workhorse.  A pair at `(i, j)` splits the
  word as `P ++ (a :: (A.word ++ b :: S))` with `|P| = i` and
  `j = i + |A.word| + 1`, where `(a, b)` is the pair's own entry in `pairs` and
  `A` is the **subtree it heads**.  Everything else in the file is a corollary
  of this one statement, including the bounds `i < j < |word|`.
* `exists_mem_pairIdx_of_mem_pairs` — the converse.  A pair known by value has a
  position, with the same decomposition.  This is the direction the labelled
  count needs, since `ConjExprMatching` hands out membership in `pairs`.
* `pairIdx_noncrossing` — **non-crossing as an inequality**.  Two pairs are
  equal, disjoint, or nested; the configuration `i < k < j < l` never occurs
  (`not_straddle`).  This is the geometric content of planarity, and it is
  forced by the shape of `wrap`: nothing in `A` can reach past `b`, and nothing
  in `B` can reach back before it.  The proof is interval arithmetic, not
  topology.
* `inside_of_fst_inside`, `inside_of_snd_inside`, `both_inside_of_mem_pairIdx` —
  a pair with **one** endpoint strictly inside `(i, j)` has **both** endpoints
  strictly inside.  This is the clause a count consumes: it is what makes "the
  pairs under a given pair" a well-defined subcollection, so that a bracket can
  be counted separately from its complement.
* `word_block_of_mem_pairIdx` — the bracketed block in `take`/`drop` form:
  `(word.drop (i+1)).take (j - i - 1)` is exactly the word of the subtree the
  pair heads, and the word is its prefix, the two entries, that block, and the
  suffix past `j`.
* `eq_of_fst_eq`, `eq_of_snd_eq`, `fst_ne_snd` — the matching is a matching:
  every position occurs in at most one pair, and on at most one side of it.
  Without these a count could double-count a letter.

Unconditional, alphabet-agnostic, and independent of small cancellation: this
file mentions no relator, no metric condition and no group.
-/

namespace GroupApproximation
namespace SmallCancellationRouter
namespace DTree

universe u

variable {β : Type u}

/-! ## 1.  Positions -/

/-- Shift both endpoints of an index pair.  A subtree's positions become the
whole tree's positions by shifting past whatever precedes it. -/
def shiftIdx (n : ℕ) (q : ℕ × ℕ) : ℕ × ℕ := (q.1 + n, q.2 + n)

@[simp] theorem shiftIdx_mk (n x y : ℕ) : shiftIdx n (x, y) = (x + n, y + n) := rfl

/-- **The matched pairs as positions in the word.**  Read off the same recursion
as `pairs`: in `wrap a b A B` the word is `a`, then `A.word`, then `b`, then
`B.word`, so the root pair occupies `0` and `|A.word| + 1`, the pairs of `A`
shift by one, and the pairs of `B` shift past the whole bracket. -/
def pairIdx : DTree β → List (ℕ × ℕ)
  | nil => []
  | wrap _ _ A B =>
      (0, A.word.length + 1)
        :: (A.pairIdx.map (shiftIdx 1)
            ++ B.pairIdx.map (shiftIdx (A.word.length + 2)))

@[simp] theorem pairIdx_nil : (nil : DTree β).pairIdx = [] := rfl

@[simp] theorem pairIdx_wrap (a b : β) (A B : DTree β) :
    (wrap a b A B).pairIdx
      = (0, A.word.length + 1)
        :: (A.pairIdx.map (shiftIdx 1)
            ++ B.pairIdx.map (shiftIdx (A.word.length + 2))) := rfl

/-- Positions and values are two readings of the same list, so they count the
same thing. -/
theorem length_pairIdx (T : DTree β) : T.pairIdx.length = T.pairs.length := by
  induction T with
  | nil => rfl
  | wrap a b A B ihA ihB =>
      simp only [pairIdx_wrap, pairs_wrap, List.length_cons, List.length_append,
        List.length_map, ihA, ihB]

/-- **Letters and positions count the same thing.**  The positional form of
`word_length`, which is the shape a count over letters consumes. -/
theorem word_length_pairIdx (T : DTree β) : T.word.length = 2 * T.pairIdx.length := by
  rw [word_length, length_pairIdx]

/-! ## 2.  Where the positions of a `wrap` come from -/

/-- The root pair of a `wrap` node occupies the two ends of the bracket. -/
theorem mem_pairIdx_root (a b : β) (A B : DTree β) :
    (0, A.word.length + 1) ∈ (wrap a b A B).pairIdx := by
  rw [pairIdx_wrap]
  exact List.mem_cons_self

/-- A position of the bracketed subtree, shifted past the opening letter. -/
theorem mem_pairIdx_left {a b : β} {A B : DTree β} {i j : ℕ}
    (h : (i, j) ∈ A.pairIdx) : (i + 1, j + 1) ∈ (wrap a b A B).pairIdx := by
  rw [pairIdx_wrap]
  exact List.mem_cons_of_mem _
    (List.mem_append_left _ (List.mem_map.mpr ⟨(i, j), h, rfl⟩))

/-- A position of the trailing subtree, shifted past the whole bracket. -/
theorem mem_pairIdx_right {a b : β} {A B : DTree β} {i j : ℕ}
    (h : (i, j) ∈ B.pairIdx) :
    (i + (A.word.length + 2), j + (A.word.length + 2))
      ∈ (wrap a b A B).pairIdx := by
  rw [pairIdx_wrap]
  exact List.mem_cons_of_mem _
    (List.mem_append_right _ (List.mem_map.mpr ⟨(i, j), h, rfl⟩))

/-- **The three places a position can come from.**  Every case analysis below
goes through this, so the `List.map` surgery happens once. -/
theorem mem_pairIdx_wrap_cases {a b : β} {A B : DTree β} {i j : ℕ}
    (h : (i, j) ∈ (wrap a b A B).pairIdx) :
    (i = 0 ∧ j = A.word.length + 1)
      ∨ (∃ i' j' : ℕ, (i', j') ∈ A.pairIdx ∧ i = i' + 1 ∧ j = j' + 1)
      ∨ (∃ i' j' : ℕ, (i', j') ∈ B.pairIdx ∧ i = i' + (A.word.length + 2)
          ∧ j = j' + (A.word.length + 2)) := by
  rw [pairIdx_wrap, List.mem_cons] at h
  rcases h with he | hm
  · simp only [Prod.mk.injEq] at he
    exact Or.inl he
  · rcases List.mem_append.mp hm with hm' | hm'
    · obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hm'
      obtain ⟨q1, q2⟩ := q
      simp only [shiftIdx_mk, Prod.mk.injEq] at hqe
      exact Or.inr (Or.inl ⟨q1, q2, hq, hqe.1.symm, hqe.2.symm⟩)
    · obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hm'
      obtain ⟨q1, q2⟩ := q
      simp only [shiftIdx_mk, Prod.mk.injEq] at hqe
      exact Or.inr (Or.inr ⟨q1, q2, hq, hqe.1.symm, hqe.2.symm⟩)

/-! ## 3.  The block a pair brackets -/

/-- **The workhorse.**  A matched pair at positions `(i, j)` cuts the word into
a prefix of length `i`, the pair's opening entry, the word of the subtree the
pair heads, the pair's closing entry, and whatever follows.

Everything positional in this file is read off this statement.  The subtree `A`
is exactly the block the pair brackets, so `j - i - 1` is its length and the
pair's own entry `(a, b)` is the one `pairs` records. -/
theorem exists_block_of_mem_pairIdx :
    ∀ (T : DTree β) (i j : ℕ), (i, j) ∈ T.pairIdx →
      ∃ (a b : β) (A : DTree β) (P S : List β),
        (a, b) ∈ T.pairs ∧
          T.word = P ++ (a :: (A.word ++ b :: S)) ∧
          P.length = i ∧ j = i + A.word.length + 1 := by
  intro T
  induction T with
  | nil =>
      intro i j h
      exact absurd h (by simp)
  | wrap a b A B ihA ihB =>
      intro i j h
      rcases mem_pairIdx_wrap_cases h with hc | hc | hc
      · obtain ⟨rfl, rfl⟩ := hc
        refine ⟨a, b, A, [], B.word, by simp, ?_, rfl, by omega⟩
        rw [word_wrap, List.nil_append]
      · obtain ⟨i₁, j₁, hm, rfl, rfl⟩ := hc
        obtain ⟨a', b', A', P', S', hp', hw', hlen', hj'⟩ := ihA i₁ j₁ hm
        refine ⟨a', b', A', a :: P', S' ++ b :: B.word, ?_, ?_, ?_, by omega⟩
        · rw [pairs_wrap, List.mem_cons]
          exact Or.inr (List.mem_append_left _ hp')
        · rw [word_wrap, hw']
          simp only [List.cons_append, List.append_assoc]
        · rw [List.length_cons, hlen']
      · obtain ⟨i₁, j₁, hm, rfl, rfl⟩ := hc
        obtain ⟨a', b', A', P', S', hp', hw', hlen', hj'⟩ := ihB i₁ j₁ hm
        refine ⟨a', b', A', a :: (A.word ++ b :: P'), S', ?_, ?_, ?_, by omega⟩
        · rw [pairs_wrap, List.mem_cons]
          exact Or.inr (List.mem_append_right _ hp')
        · rw [word_wrap, hw']
          simp only [List.cons_append, List.append_assoc]
        · simp only [List.length_cons, List.length_append]
          omega

/-- **A pair opens before it closes, and closes inside the word.** -/
theorem lt_of_mem_pairIdx {T : DTree β} {i j : ℕ} (h : (i, j) ∈ T.pairIdx) :
    i < j ∧ j < T.word.length := by
  obtain ⟨a, b, A, P, S, -, hw, hlen, hj⟩ := exists_block_of_mem_pairIdx T i j h
  have hlenw := congrArg List.length hw
  simp only [List.length_append, List.length_cons] at hlenw
  omega

/-- **The converse of the workhorse.**  A pair known by its two entries has a
position, with the same decomposition of the word.

`ConjExprMatching` hands out membership in `pairs` — that is where the block
labels live — so a count that wants to know *where* a labelled pair sits enters
through this statement. -/
theorem exists_mem_pairIdx_of_mem_pairs :
    ∀ (T : DTree β) (p : β × β), p ∈ T.pairs →
      ∃ (i j : ℕ) (A : DTree β) (P S : List β),
        (i, j) ∈ T.pairIdx ∧
          T.word = P ++ (p.1 :: (A.word ++ p.2 :: S)) ∧
          P.length = i ∧ j = i + A.word.length + 1 := by
  intro T
  induction T with
  | nil =>
      intro p h
      exact absurd h (by simp)
  | wrap a b A B ihA ihB =>
      intro p h
      rw [pairs_wrap, List.mem_cons] at h
      rcases h with rfl | h
      · refine ⟨0, A.word.length + 1, A, [], B.word, mem_pairIdx_root a b A B,
          ?_, rfl, by omega⟩
        show (wrap a b A B).word = [] ++ (a :: (A.word ++ b :: B.word))
        rw [word_wrap, List.nil_append]
      · rcases List.mem_append.mp h with h' | h'
        · obtain ⟨i₁, j₁, A', P', S', hm', hw', hlen', hj'⟩ := ihA p h'
          refine ⟨i₁ + 1, j₁ + 1, A', a :: P', S' ++ b :: B.word,
            mem_pairIdx_left hm', ?_, ?_, by omega⟩
          · rw [word_wrap, hw']
            simp only [List.cons_append, List.append_assoc]
          · rw [List.length_cons, hlen']
        · obtain ⟨i₁, j₁, A', P', S', hm', hw', hlen', hj'⟩ := ihB p h'
          refine ⟨i₁ + (A.word.length + 2), j₁ + (A.word.length + 2), A',
            a :: (A.word ++ b :: P'), S', mem_pairIdx_right hm', ?_, ?_,
            by omega⟩
          · rw [word_wrap, hw']
            simp only [List.cons_append, List.append_assoc]
          · simp only [List.length_cons, List.length_append]
            omega

/-! ## 4.  Non-crossing, as an inequality -/

/-- **Planarity, stated arithmetically.**  Any two matched pairs are equal, lie
in disjoint stretches, or one is nested inside the other.  There is no fourth
possibility, and in particular `i < k < j < l` never occurs.

The proof is the `wrap` recursion and nothing else: the root pair spans the
whole bracket, everything from the bracketed subtree lies strictly inside it,
and everything from the trailing subtree lies strictly after it.  So the three
sources are already separated by intervals, and each source is separated
internally by the inductive hypothesis. -/
theorem pairIdx_noncrossing :
    ∀ (T : DTree β) (i j k l : ℕ), (i, j) ∈ T.pairIdx → (k, l) ∈ T.pairIdx →
      (i = k ∧ j = l) ∨ j < k ∨ l < i ∨ (i < k ∧ l < j) ∨ (k < i ∧ j < l) := by
  intro T
  induction T with
  | nil =>
      intro i j k l h _
      exact absurd h (by simp)
  | wrap a b A B ihA ihB =>
      intro i j k l h₁ h₂
      rcases mem_pairIdx_wrap_cases h₁ with hc₁ | hc₁ | hc₁
      · obtain ⟨rfl, rfl⟩ := hc₁
        rcases mem_pairIdx_wrap_cases h₂ with hc₂ | hc₂ | hc₂
        · obtain ⟨rfl, rfl⟩ := hc₂
          omega
        · obtain ⟨k₁, l₁, hm₂, rfl, rfl⟩ := hc₂
          have hb₂ := lt_of_mem_pairIdx hm₂
          omega
        · obtain ⟨k₁, l₁, hm₂, rfl, rfl⟩ := hc₂
          have hb₂ := lt_of_mem_pairIdx hm₂
          omega
      · obtain ⟨i₁, j₁, hm₁, rfl, rfl⟩ := hc₁
        have hb₁ := lt_of_mem_pairIdx hm₁
        rcases mem_pairIdx_wrap_cases h₂ with hc₂ | hc₂ | hc₂
        · obtain ⟨rfl, rfl⟩ := hc₂
          omega
        · obtain ⟨k₁, l₁, hm₂, rfl, rfl⟩ := hc₂
          have hb₂ := lt_of_mem_pairIdx hm₂
          have hIH := ihA i₁ j₁ k₁ l₁ hm₁ hm₂
          omega
        · obtain ⟨k₁, l₁, hm₂, rfl, rfl⟩ := hc₂
          have hb₂ := lt_of_mem_pairIdx hm₂
          omega
      · obtain ⟨i₁, j₁, hm₁, rfl, rfl⟩ := hc₁
        have hb₁ := lt_of_mem_pairIdx hm₁
        rcases mem_pairIdx_wrap_cases h₂ with hc₂ | hc₂ | hc₂
        · obtain ⟨rfl, rfl⟩ := hc₂
          omega
        · obtain ⟨k₁, l₁, hm₂, rfl, rfl⟩ := hc₂
          have hb₂ := lt_of_mem_pairIdx hm₂
          omega
        · obtain ⟨k₁, l₁, hm₂, rfl, rfl⟩ := hc₂
          have hb₂ := lt_of_mem_pairIdx hm₂
          have hIH := ihB i₁ j₁ k₁ l₁ hm₁ hm₂
          omega

/-- **No pair straddles another.**  The forbidden configuration, named. -/
theorem not_straddle {T : DTree β} {i j k l : ℕ}
    (h₁ : (i, j) ∈ T.pairIdx) (h₂ : (k, l) ∈ T.pairIdx) :
    ¬ (i < k ∧ k < j ∧ j < l) := by
  have hnc := pairIdx_noncrossing T i j k l h₁ h₂
  omega

/-! ## 5.  What lies inside a bracket -/

/-- **One endpoint inside forces the other inside.**  Stated at the opening
endpoint: if a pair opens strictly inside `(i, j)` it also closes strictly
inside it.

This is the clause a count runs on.  It says the pairs under a given pair form a
subcollection closed under nothing more than looking at one endpoint, so a
bracket can be counted apart from its complement without ever checking the far
end of a pair. -/
theorem inside_of_fst_inside {T : DTree β} {i j k l : ℕ}
    (h₁ : (i, j) ∈ T.pairIdx) (h₂ : (k, l) ∈ T.pairIdx)
    (hik : i < k) (hkj : k < j) : i < l ∧ l < j := by
  have hb₂ := lt_of_mem_pairIdx h₂
  have hnc := pairIdx_noncrossing T i j k l h₁ h₂
  omega

/-- The same at the closing endpoint. -/
theorem inside_of_snd_inside {T : DTree β} {i j k l : ℕ}
    (h₁ : (i, j) ∈ T.pairIdx) (h₂ : (k, l) ∈ T.pairIdx)
    (hil : i < l) (hlj : l < j) : i < k ∧ k < j := by
  have hb₂ := lt_of_mem_pairIdx h₂
  have hnc := pairIdx_noncrossing T i j k l h₁ h₂
  omega

/-- **Either endpoint inside puts both inside.**  The two statements above in
the form a count quantifies over: one hypothesis, both conclusions. -/
theorem both_inside_of_mem_pairIdx {T : DTree β} {i j k l : ℕ}
    (h₁ : (i, j) ∈ T.pairIdx) (h₂ : (k, l) ∈ T.pairIdx)
    (hin : (i < k ∧ k < j) ∨ (i < l ∧ l < j)) :
    i < k ∧ k < j ∧ i < l ∧ l < j := by
  rcases hin with ⟨h, h'⟩ | ⟨h, h'⟩
  · obtain ⟨hl, hl'⟩ := inside_of_fst_inside h₁ h₂ h h'
    exact ⟨h, h', hl, hl'⟩
  · obtain ⟨hk, hk'⟩ := inside_of_snd_inside h₁ h₂ h h'
    exact ⟨hk, hk', h, h'⟩

/-! ## 6.  The bracketed block, in prefix form -/

/-- **The block a pair brackets, read off the word.**  For a pair at `(i, j)`:
the word is its prefix of length `i`, the opening entry, the block, the closing
entry, and the suffix past `j`; and the block is exactly
`(word.drop (i + 1)).take (j - i - 1)`, the word of the subtree the pair heads.

`take`/`drop` rather than `getElem`, because the rest of the lane is written
with prefixes and infixes. -/
theorem word_block_of_mem_pairIdx {T : DTree β} {i j : ℕ}
    (h : (i, j) ∈ T.pairIdx) :
    ∃ (a b : β) (A : DTree β),
      (a, b) ∈ T.pairs ∧
        j = i + A.word.length + 1 ∧
        (T.word.drop (i + 1)).take (j - i - 1) = A.word ∧
        T.word.take i ++ (a :: (A.word ++ b :: T.word.drop (j + 1))) = T.word := by
  obtain ⟨a, b, A, P, S, hp, hw, hlen, hj⟩ := exists_block_of_mem_pairIdx T i j h
  refine ⟨a, b, A, hp, hj, ?_, ?_⟩
  · have hw2 : T.word = (P ++ [a]) ++ (A.word ++ (b :: S)) := by
      rw [hw]
      simp only [List.cons_append, List.append_assoc, List.nil_append]
    have hlen2 : (P ++ [a]).length = i + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hdrop : T.word.drop (i + 1) = A.word ++ (b :: S) := by
      rw [hw2, ← hlen2, List.drop_left]
    rw [hdrop, show j - i - 1 = A.word.length from by omega, List.take_left]
  · have htake : T.word.take i = P := by
      rw [hw, ← hlen, List.take_left]
    have hw3 : T.word = (P ++ (a :: (A.word ++ [b]))) ++ S := by
      rw [hw]
      simp only [List.cons_append, List.append_assoc, List.nil_append]
    have hlen3 : (P ++ (a :: (A.word ++ [b]))).length = j + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hdrop : T.word.drop (j + 1) = S := by
      rw [hw3, ← hlen3, List.drop_left]
    rw [htake, hdrop]
    exact hw.symm

/-! ## 7.  It is a matching -/

/-- A position opens at most one pair. -/
theorem eq_of_fst_eq {T : DTree β} {i j l : ℕ}
    (h₁ : (i, j) ∈ T.pairIdx) (h₂ : (i, l) ∈ T.pairIdx) : j = l := by
  have hb₁ := lt_of_mem_pairIdx h₁
  have hb₂ := lt_of_mem_pairIdx h₂
  have hnc := pairIdx_noncrossing T i j i l h₁ h₂
  omega

/-- A position closes at most one pair. -/
theorem eq_of_snd_eq {T : DTree β} {i k j : ℕ}
    (h₁ : (i, j) ∈ T.pairIdx) (h₂ : (k, j) ∈ T.pairIdx) : i = k := by
  have hb₁ := lt_of_mem_pairIdx h₁
  have hb₂ := lt_of_mem_pairIdx h₂
  have hnc := pairIdx_noncrossing T i j k j h₁ h₂
  omega

/-- A position is never both an opening and a closing endpoint, so every letter
carries a definite side of its pair.  Without this a count could take one letter
for two. -/
theorem fst_ne_snd {T : DTree β} {i j k : ℕ}
    (h₁ : (i, j) ∈ T.pairIdx) (h₂ : (k, i) ∈ T.pairIdx) : False := by
  have hb₁ := lt_of_mem_pairIdx h₁
  have hb₂ := lt_of_mem_pairIdx h₂
  have hnc := pairIdx_noncrossing T i j k i h₁ h₂
  omega

end DTree
end SmallCancellationRouter
end GroupApproximation
