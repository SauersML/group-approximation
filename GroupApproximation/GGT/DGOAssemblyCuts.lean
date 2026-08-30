import GroupApproximation.GGT.DGOAssemblyHalves

/-!
# Cuts of the two halves, built by concatenation

The halves of `GGT/DGOAssemblyHalves.lean` are words; to be polygons they need
cut functions, and the cut of each is an assembly of three ingredients: the cut
inherited from the original polygon on an arc, the identity cut on the chord,
and a concatenation operation joining two cuts end to end.

## Why concatenation rather than a piecewise formula

Written directly, the first half's cut is a two-branch formula and the second
half's a three-branch one, each needing its own monotonicity argument through
its own `ite` --- and `omega` does not split an `ite`, so each branch has to be
opened by hand.  Building them out of `appendCut` costs one `ite` argument,
proved once, and the two halves are then assembled with no arithmetic at all.
The second half is `(w.drop (c b) ++ w.take (c a)) ++ t`, so it is the same
operation twice.

## The chord is cut into single letters

`isPolygonCut_id` gives each letter of the chord its own side.  That is free ---
a single-letter side satisfies the quasi-geodesic clause automatically once
`1 ≤ b`, the same observation that closes the exempt-side gap in
`GGT/DGOSumBoundFinite.lean` --- and it is what the later construction needs
anyway, since the chord's components and the maximal subpaths between them
become sides of types (4) and (5) of the cycles `c_j`.

It is also where the chord's length enters the side count: the halves have
`(b − a) + ℓ(t)` and `(n − b + a) + ℓ(t)` sides, so cutting costs `2ℓ(t)` sides
in total.  That is the overhead the calculus lemma absorbs.
-/

namespace GroupApproximation
namespace GGT
namespace DGOPolygonCut

open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Three ingredients -/

/-- **Insert one graph vertex into a polygon cut.**  If `i` lies on side `t`,
the old side `[c t,c (t+1)]` becomes the two sides `[c t,i]` and
`[i,c (t+1)]`.  All later corners are shifted by one. -/
def insertPointCut (c : ℕ → ℕ) (t i : ℕ) : ℕ → ℕ :=
  fun s => if s ≤ t then c s else if s = t + 1 then i else c (s - 1)

omit [Group G] in
/-- **Inserting a vertex lying on a side adds exactly one side.** -/
theorem isPolygonCut_insertPoint {w : List (RelLetter G Λ)} {c : ℕ → ℕ}
    {n t i : ℕ} (h : IsPolygonCut n w c) (ht : t < n)
    (hti : c t ≤ i) (hit : i ≤ c (t + 1)) :
    IsPolygonCut (n + 1) w (insertPointCut c t i) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [insertPointCut, h.start]
  · unfold insertPointCut
    rw [if_neg (by omega : ¬ n + 1 ≤ t),
      if_neg (by omega : n + 1 ≠ t + 1), show n + 1 - 1 = n from by omega,
      h.finish]
  · intro s
    by_cases hbefore : s + 1 ≤ t
    · unfold insertPointCut
      rw [if_pos (by omega : s ≤ t), if_pos hbefore]
      exact h.mono s
    · by_cases hat : s ≤ t
      · have hs : t = s := by omega
        subst hs
        unfold insertPointCut
        rw [if_pos le_rfl, if_neg (by omega : ¬ s + 1 ≤ s), if_pos rfl]
        exact hti
      · by_cases hnew : s = t + 1
        · subst hnew
          unfold insertPointCut
          rw [if_neg (by omega : ¬ t + 1 ≤ t), if_pos rfl,
            if_neg (by omega : ¬ t + 1 + 1 ≤ t),
            if_neg (by omega : t + 1 + 1 ≠ t + 1),
            show t + 1 + 1 - 1 = t + 1 from by omega]
          exact hit
        · unfold insertPointCut
          rw [if_neg (by omega : ¬ s ≤ t), if_neg hnew,
            if_neg (by omega : ¬ s + 1 ≤ t),
            if_neg (by omega : s + 1 ≠ t + 1),
            show s + 1 - 1 = (s - 1) + 1 from by omega]
          exact h.mono (s - 1)

/-- **Insert the two graph vertices of an interior balanced cut.**

The second selected side has index `b+1` after the first insertion.  Keeping
this definition as the composition of two one-point refinements makes the
`+2` side cost definitional and lets all existing corner-to-corner assembly
lemmas apply unchanged to the refined cut. -/
def splitPairCut (c : ℕ → ℕ) (a b i j : ℕ) : ℕ → ℕ :=
  insertPointCut (insertPointCut c a i) (b + 1) j

omit [Group G] in
/-- **The two interior vertices refine an `n`-gon to an `(n+2)`-gon.** -/
theorem isPolygonCut_splitPair {w : List (RelLetter G Λ)} {c : ℕ → ℕ}
    {n a b i j : ℕ} (h : IsPolygonCut n w c) (hab : a < b) (hbn : b < n)
    (hai : c a ≤ i) (hia : i ≤ c (a + 1))
    (hbj : c b ≤ j) (hjb : j ≤ c (b + 1)) :
    IsPolygonCut (n + 2) w (splitPairCut c a b i j) := by
  have hfirst : IsPolygonCut (n + 1) w (insertPointCut c a i) :=
    isPolygonCut_insertPoint h (by omega) hai hia
  have hleft : insertPointCut c a i (b + 1) = c b := by
    rw [insertPointCut, if_neg (by omega : ¬ b + 1 ≤ a),
      if_neg (by omega : b + 1 ≠ a + 1), show b + 1 - 1 = b from by omega]
  have hright : insertPointCut c a i (b + 1 + 1) = c (b + 1) := by
    rw [insertPointCut, if_neg (by omega : ¬ b + 1 + 1 ≤ a),
      if_neg (by omega : b + 1 + 1 ≠ a + 1),
      show b + 1 + 1 - 1 = b + 1 from by omega]
  apply isPolygonCut_insertPoint hfirst (by omega)
  · rwa [hleft]
  · rwa [hright]

omit [Group G] in
/-- The first inserted point is corner `a+1` of the refined cut. -/
@[simp] theorem splitPairCut_left {c : ℕ → ℕ} {a b i j : ℕ} (hab : a < b) :
    splitPairCut c a b i j (a + 1) = i := by
  rw [splitPairCut, insertPointCut, if_pos (by omega : a + 1 ≤ b + 1),
    insertPointCut, if_neg (by omega : ¬ a + 1 ≤ a), if_pos rfl]

omit [Group G] in
/-- The second inserted point is corner `b+2` of the refined cut. -/
@[simp] theorem splitPairCut_right {c : ℕ → ℕ} {a b i j : ℕ} :
    splitPairCut c a b i j (b + 2) = j := by
  rw [splitPairCut, insertPointCut, if_neg (by omega : ¬ b + 2 ≤ b + 1),
    if_pos (by omega : b + 2 = b + 1 + 1)]

/-- The two selected graph vertices are the corresponding refined corners. -/
theorem cutVertex_splitPair_left (v : G) (w : List (RelLetter G Λ))
    (c : ℕ → ℕ) {a b i j : ℕ} (hab : a < b) :
    cutVertex v w (splitPairCut c a b i j) (a + 1) = vertex v w i := by
  rw [cutVertex_apply, splitPairCut_left hab]

/-- The second selected graph vertex is likewise a refined corner. -/
theorem cutVertex_splitPair_right (v : G) (w : List (RelLetter G Λ))
    (c : ℕ → ℕ) (a b i j : ℕ) :
    cutVertex v w (splitPairCut c a b i j) (b + 2) = vertex v w j := by
  rw [cutVertex_apply, splitPairCut_right]

/-- **Two cuts, joined end to end.** -/
def appendCut (c₁ : ℕ → ℕ) (n₁ : ℕ) (c₂ : ℕ → ℕ) : ℕ → ℕ :=
  fun s => if s ≤ n₁ then c₁ s else c₁ n₁ + c₂ (s - n₁)

omit [Group G] in
/-- **The concatenation of two cuts cuts the concatenation.** -/
theorem isPolygonCut_append {u z : List (RelLetter G Λ)} {n₁ n₂ : ℕ}
    {c₁ c₂ : ℕ → ℕ} (h₁ : IsPolygonCut n₁ u c₁) (h₂ : IsPolygonCut n₂ z c₂) :
    IsPolygonCut (n₁ + n₂) (u ++ z) (appendCut c₁ n₁ c₂) := by
  refine ⟨?_, ?_, ?_⟩
  · show (if 0 ≤ n₁ then c₁ 0 else c₁ n₁ + c₂ (0 - n₁)) = 0
    rw [if_pos (Nat.zero_le n₁)]
    exact h₁.start
  · show (if n₁ + n₂ ≤ n₁ then c₁ (n₁ + n₂)
        else c₁ n₁ + c₂ (n₁ + n₂ - n₁)) = (u ++ z).length
    rw [List.length_append]
    by_cases hz : n₂ = 0
    · subst hz
      rw [if_pos (by omega : n₁ + 0 ≤ n₁)]
      have hzlen : z.length = 0 := by
        have := h₂.finish
        rw [h₂.start] at this
        omega
      have harg : n₁ + 0 = n₁ := by omega
      rw [harg, h₁.finish]
      omega
    · rw [if_neg (by omega : ¬ (n₁ + n₂ ≤ n₁))]
      have harg : n₁ + n₂ - n₁ = n₂ := by omega
      rw [harg, h₁.finish, h₂.finish]
  · intro s
    show (if s ≤ n₁ then c₁ s else c₁ n₁ + c₂ (s - n₁))
      ≤ (if s + 1 ≤ n₁ then c₁ (s + 1) else c₁ n₁ + c₂ (s + 1 - n₁))
    by_cases h1 : s + 1 ≤ n₁
    · rw [if_pos (by omega : s ≤ n₁), if_pos h1]
      exact h₁.mono s
    · rw [if_neg h1]
      by_cases h0 : s ≤ n₁
      · rw [if_pos h0]
        have hs : s = n₁ := by omega
        subst hs
        omega
      · rw [if_neg h0]
        have harg : s + 1 - n₁ = (s - n₁) + 1 := by omega
        rw [harg]
        have hm := h₂.mono (s - n₁)
        omega

omit [Group G] in
/-- **Every letter its own side.** -/
theorem isPolygonCut_id (z : List (RelLetter G Λ)) :
    IsPolygonCut z.length z (fun s => s) :=
  ⟨rfl, rfl, fun s => Nat.le_succ s⟩

omit [Group G] in
/-- **The cut of the polygon, restricted to an arc.**  The corners of the arc
are the corners of the polygon, renumbered from the arc's own start. -/
theorem isPolygonCut_arcWord {w : List (RelLetter G Λ)} {c : ℕ → ℕ} {n a b : ℕ}
    (h : IsPolygonCut n w c) (hab : a ≤ b) (hbn : b ≤ n) :
    IsPolygonCut (b - a) (arcWord w c a b) (fun s => c (a + s) - c a) := by
  refine ⟨?_, ?_, ?_⟩
  · show c (a + 0) - c a = 0
    have harg : a + 0 = a := by omega
    rw [harg]
    omega
  · show c (a + (b - a)) - c a = (arcWord w c a b).length
    have harg : a + (b - a) = b := by omega
    rw [harg, length_arcWord w c (h.le_length hbn)]
  · intro s
    show c (a + s) - c a ≤ c (a + (s + 1)) - c a
    have harg : a + (s + 1) = (a + s) + 1 := by omega
    rw [harg]
    have hm := h.mono (a + s)
    omega

omit [Group G] in
/-- **The cut of the polygon, restricted to a prefix.**  The cut function does
not even change: the corners of the prefix are the corners of the polygon. -/
theorem isPolygonCut_take {w : List (RelLetter G Λ)} {c : ℕ → ℕ} {n a : ℕ}
    (h : IsPolygonCut n w c) (ha : a ≤ n) :
    IsPolygonCut a (w.take (c a)) c := by
  refine ⟨h.start, ?_, h.mono⟩
  show c a = (w.take (c a)).length
  rw [List.length_take]
  have hle := h.le_length ha
  omega

omit [Group G] in
/-- **The arc that runs to the last corner is the whole suffix.** -/
theorem arcWord_last (w : List (RelLetter G Λ)) {c : ℕ → ℕ} {n b : ℕ}
    (h : IsPolygonCut n w c) : arcWord w c b n = w.drop (c b) := by
  show (w.drop (c b)).take (c n - c b) = w.drop (c b)
  have hlen : (w.drop (c b)).length = c n - c b := by
    rw [List.length_drop, h.finish]
  rw [← hlen]
  exact List.take_length

/-! ## The two halves, cut -/

/-- **The first half is a polygon** with `(b − a) + ℓ(t)` sides: the sides of the
original polygon from corner `a` to corner `b`, then one side per letter of the
chord. -/
theorem isPolygonCut_firstHalf {w : List (RelLetter G Λ)} {c : ℕ → ℕ} {n a b : ℕ}
    (h : IsPolygonCut n w c) (hab : a ≤ b) (hbn : b ≤ n)
    (t : List (RelLetter G Λ)) :
    IsPolygonCut ((b - a) + t.length) (firstHalf w c a b t)
      (appendCut (fun s => c (a + s) - c a) (b - a) (fun s => s)) := by
  have hid : IsPolygonCut t.length (revWord t) (fun s => s) := by
    have h0 := isPolygonCut_id (revWord t)
    rwa [length_revWord] at h0
  exact isPolygonCut_append (isPolygonCut_arcWord h hab hbn) hid

omit [Group G] in
/-- **The second half is a polygon** with `(n − b) + a + ℓ(t)` sides.  Two
concatenations, because the second arc wraps past the end of the word. -/
theorem isPolygonCut_secondHalf {w : List (RelLetter G Λ)} {c : ℕ → ℕ} {n a b : ℕ}
    (h : IsPolygonCut n w c) (han : a ≤ n) (hbn : b ≤ n)
    (t : List (RelLetter G Λ)) :
    IsPolygonCut ((n - b) + a + t.length) (secondHalf w c a b t)
      (appendCut (appendCut (fun s => c (b + s) - c b) (n - b) c) ((n - b) + a)
        (fun s => s)) := by
  have hdrop : IsPolygonCut (n - b) (w.drop (c b)) (fun s => c (b + s) - c b) := by
    have h0 := isPolygonCut_arcWord h hbn (le_refl n)
    rwa [arcWord_last w h] at h0
  have hpre : IsPolygonCut ((n - b) + a) (w.drop (c b) ++ w.take (c a))
      (appendCut (fun s => c (b + s) - c b) (n - b) c) :=
    isPolygonCut_append hdrop (isPolygonCut_take h han)
  have hid : IsPolygonCut t.length t (fun s => s) := isPolygonCut_id t
  exact isPolygonCut_append hpre hid

end DGOPolygonCut
end GGT
end GroupApproximation
