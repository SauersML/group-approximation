import GroupApproximation.GGT.DGOIsolatedComponentBridge
import GroupApproximation.GGT.OsinTheorem54SepPolygonVertex
import GroupApproximation.GGT.OsinTheorem54SepFourGonPinning

/-!
# Cutting a polygon along a chord: the word, and dropping a trivial side

Dahmani--Guirardel--Osin's Lemma 4.17 cuts an `n`-gon `p₀ … p_{n-1}` along a
geodesic `q` from `x₀` to `x₃`, producing a 4-gon `p₀ p₁ p₂ q⁻¹` and an
`(n-1)`-gon on the other side.  Both are of the form

    joinWord w m q = w.take m ++ q ,

a prefix of the original word followed by the chord, and this module supplies
that word with the facts every polygon argument needs of it: length, letters,
what it spells, its vertices and its letters in each of the two ranges.  It is
the same shape as `cutWord` (`DGOIsolatedComponentCut`) and `normWord`
(`…Normalise`) with the single closing letter replaced by an arbitrary word, and
the same discipline: indices are parameters carrying equations, so that no caller
ever rewrites under `getElem`.

Concept grep before writing: `take … ++`, `++ revWord` across the tree.  What
exists is the four-block quadrilateral `p ++ q ++ r ++ revWord s`
(`OsinTheorem54SepPolygonVertex`, `…SepFourGonPinning`), whose blocks are given
rather than cut out of one word, and my own `cutWord` / `normWord`, whose second
block is a single letter.  Neither is this.

## Dropping a trivial side

`baseCase_of_dropEmpty` is the other half, and it is what keeps the cut honest.
The cut of an `n`-gon needs the corners `c 1`, `c 2`, `c 3` to be distinct from
`c 0` and from each other; when a side is trivial they are not, and the maximality
of the distinguished component can fail in the cut polygon — its successor letter
is then the first letter of the chord, which may be a `lam`-letter.  Rather than
patch that, the induction sheds the trivial side first: deleting a corner whose
two ends coincide merges two sides of which one is empty, so the surviving side
is unchanged and the clause is quoted verbatim.  A polygon with a trivial side is
one with fewer sides, and the base case at `n - 1` applies to it.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The joined word -/

/-- **A prefix of `w` followed by a chord `q`.**  Read from `v`, this is the
polygon cut off by `q` from the first `m` letters of `w`. -/
def joinWord (w : List (RelLetter G Λ)) (m : ℕ) (q : List (RelLetter G Λ)) :
    List (RelLetter G Λ) :=
  w.take m ++ q

omit [Group G] in
/-- The joined word has `m + |q|` letters. -/
theorem length_joinWord (w : List (RelLetter G Λ)) {m : ℕ} (q : List (RelLetter G Λ))
    (hm : m ≤ w.length) : (joinWord w m q).length = m + q.length := by
  show (w.take m ++ q).length = m + q.length
  rw [List.length_append, List.length_take_of_le hm]

/-- Its letters are those of `w` and of `q`. -/
theorem letters_joinWord (D : RelGenSet G Λ) {w : List (RelLetter G Λ)}
    (hlet : ∀ a ∈ w, D.IsLetter a) (m : ℕ) {q : List (RelLetter G Λ)}
    (hq : ∀ a ∈ q, D.IsLetter a) : ∀ a ∈ joinWord w m q, D.IsLetter a := by
  intro a ha
  have ha' : a ∈ w.take m ++ q := ha
  rcases List.mem_append.mp ha' with h | h
  · exact hlet a (List.take_subset m w h)
  · exact hq a h

/-- It spells the prefix followed by the chord. -/
theorem listVal_joinWord (w : List (RelLetter G Λ)) (m : ℕ)
    (q : List (RelLetter G Λ)) :
    RelLetter.listVal (joinWord w m q)
      = RelLetter.listVal (w.take m) * RelLetter.listVal q := by
  show RelLetter.listVal (w.take m ++ q) = _
  rw [listVal_append]

/-- **The joined word is closed** when the chord spells the way back.  This is
how the cut polygon closes: `q` runs from `vertex v w m` to `v`. -/
theorem listVal_joinWord_eq_one (v : G) (w : List (RelLetter G Λ)) (m : ℕ)
    (q : List (RelLetter G Λ))
    (hq : RelLetter.listVal q = (vertex v w m)⁻¹ * v) :
    RelLetter.listVal (joinWord w m q) = 1 := by
  rw [listVal_joinWord, hq, vertex_eq_mul_listVal_take w v m]
  group

/-! ## Its vertices -/

/-- Before the chord, the vertices are those of `w`. -/
theorem vertex_joinWord_le (v : G) (w : List (RelLetter G Λ)) {m : ℕ}
    (q : List (RelLetter G Λ)) (hm : m ≤ w.length) (p : ℕ) (hp : p ≤ m) :
    vertex v (joinWord w m q) p = vertex v w p := by
  show vertex v (w.take m ++ q) p = vertex v w p
  rw [vertex_append_of_le (w.take m) q v p
      (by rw [List.length_take_of_le hm]; exact hp),
    vertex_take_eq v w m p hp]

/-- On the chord, they are the vertices of `q` read from `vertex v w m`. -/
theorem vertex_joinWord_add (v : G) (w : List (RelLetter G Λ)) {m : ℕ}
    (q : List (RelLetter G Λ)) (hm : m ≤ w.length) (p t : ℕ)
    (hpt : p = m + t) :
    vertex v (joinWord w m q) p = vertex (vertex v w m) q t := by
  show vertex v (w.take m ++ q) p = _
  rw [show p = (w.take m).length + t from by
      rw [List.length_take_of_le hm]; omega,
    vertex_append_add (w.take m) q v t, ← vertex_eq_mul_listVal_take w v m]

/-! ## Its letters -/

omit [Group G] in
/-- Before the chord, the letters are those of `w`. -/
theorem getElem_joinWord_lt (w : List (RelLetter G Λ)) {m : ℕ}
    (q : List (RelLetter G Λ)) (hm : m ≤ w.length) (p : ℕ) (hpm : p < m)
    (hp : p < (joinWord w m q).length) (hpw : p < w.length) :
    (joinWord w m q)[p]'hp = w[p]'hpw := by
  have h1 : (joinWord w m q)[p]? = w[p]? := by
    show (w.take m ++ q)[p]? = w[p]?
    rw [List.getElem?_append_left (by rw [List.length_take_of_le hm]; omega),
      List.getElem?_take_of_lt hpm]
  rw [List.getElem?_eq_getElem hp, List.getElem?_eq_getElem hpw] at h1
  exact Option.some.inj h1

omit [Group G] in
/-- On the chord, they are the letters of `q`. -/
theorem getElem_joinWord_add (w : List (RelLetter G Λ)) {m : ℕ}
    (q : List (RelLetter G Λ)) (hm : m ≤ w.length) (p t : ℕ) (hpt : p = m + t)
    (hp : p < (joinWord w m q).length) (ht : t < q.length) :
    (joinWord w m q)[p]'hp = q[t]'ht := by
  have h1 : (joinWord w m q)[p]? = q[t]? := by
    show (w.take m ++ q)[p]? = q[t]?
    rw [List.getElem?_append_right
        (by rw [List.length_take_of_le hm]; omega),
      List.length_take_of_le hm, show p - m = t from by omega]
  rw [List.getElem?_eq_getElem hp, List.getElem?_eq_getElem ht] at h1
  exact Option.some.inj h1

/-! ## Dropping a trivial side -/

/-- **A polygon with a trivial side is a polygon with one side fewer.**

Deleting the corner `j + 1` when the side `[c (j+1), c (j+2)]` is trivial leaves
every side unchanged: the sides before `j + 1` are untouched, and the side that
would be merged with the empty one is `[c j, c (j+1)] = [c j, c (j+2)]`.  So a
base case at `N` gives one at `N + 1` for polygons carrying a trivial side, and
the induction of Lemma 4.17 can assume every side is non-trivial.

The distinguished side `0` is never the trivial one --- `IsComp` asks
`c 0 < c 1` --- so the deletion never touches it. -/
theorem baseCase_of_dropEmpty (D : RelGenSet G Λ) (mu b : ℝ) (C : ℕ) {N : ℕ}
    (hbase : ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 →
      c N = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) → ∀ lam : Λ,
      (∀ s : ℕ, s < N → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
        q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w p)
              (vertex v w q) : ℕ) : ℝ)) →
      IsComp lam w (c 0) (c 1) → IsIsolated D.fam lam v w (c 0) →
        (vertex v w (c 0))⁻¹ * vertex v w (c 1) ∈ D.relBall lam (C * N))
    (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ)
    (hlet : ∀ a ∈ w, D.IsLetter a) (hclosed : RelLetter.listVal w = 1)
    (hc0 : c 0 = 0) (hcN : c (N + 1) = w.length)
    (hcmono : ∀ s : ℕ, c s ≤ c (s + 1)) (lam : Λ)
    (hcqg : ∀ s : ℕ, s < N + 1 → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
      q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
        ≤ ((wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) : ℕ) : ℝ))
    (hcomp : IsComp lam w (c 0) (c 1)) (hiso : IsIsolated D.fam lam v w (c 0))
    {j : ℕ} (hj : j < N) (hj0 : j ≠ 0) (hempty : c j = c (j + 1)) :
    (vertex v w (c 0))⁻¹ * vertex v w (c 1) ∈ D.relBall lam (C * N) := by
  -- the cut function with the corner `j` deleted
  set e : ℕ → ℕ := fun s => if s < j then c s else c (s + 1)
  have hev : ∀ s : ℕ, e s = if s < j then c s else c (s + 1) := fun s => rfl
  have helt : ∀ s : ℕ, s < j → e s = c s := by
    intro s hs
    rw [hev s, if_pos hs]
  have hege : ∀ s : ℕ, j ≤ s → e s = c (s + 1) := by
    intro s hs
    rw [hev s, if_neg (by omega)]
  have he0 : e 0 = 0 := by rw [helt 0 (by omega), hc0]
  have he1 : e 1 = c 1 := by
    rcases Nat.lt_or_ge 1 j with h | h
    · exact helt 1 h
    · have hj1 : j = 1 := by omega
      have hc12 : c 1 = c (1 + 1) := by subst hj1; exact hempty
      rw [hege 1 (by omega)]
      exact hc12.symm
  have heN : e N = w.length := by rw [hege N (by omega), hcN]
  have hemono : ∀ s : ℕ, e s ≤ e (s + 1) := by
    intro s
    rcases Nat.lt_or_ge (s + 1) j with h | h
    · rw [helt s (by omega), helt (s + 1) h]
      exact hcmono s
    · rcases Nat.lt_or_ge s j with h2 | h2
      · have h3 : s + 1 = j := by omega
        rw [helt s h2, hege (s + 1) (by omega), h3, ← hempty, ← h3]
        exact hcmono s
      · rw [hege s h2, hege (s + 1) (by omega)]
        exact hcmono (s + 1)
  have heqg : ∀ s : ℕ, s < N → s ≠ 0 → ∀ p q : ℕ, e s ≤ p → p ≤ q →
      q ≤ e (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
        ≤ ((wordDist D.alphabet.carrier (vertex v w p)
            (vertex v w q) : ℕ) : ℝ) := by
    intro s hs hs0 p q hp hpq hq
    rcases Nat.lt_or_ge (s + 1) j with h | h
    · rw [helt s (by omega)] at hp
      rw [helt (s + 1) h] at hq
      exact hcqg s (by omega) hs0 p q hp hpq hq
    · rcases Nat.lt_or_ge s j with h2 | h2
      · -- the corner after side `s` is the deleted one, and it is where side
        -- `s` already ended
        have h3 : s + 1 = j := by omega
        rw [helt s h2] at hp
        rw [hege (s + 1) (by omega), h3, ← hempty] at hq
        exact hcqg s (by omega) hs0 p q hp hpq (by rw [h3]; exact hq)
      · rw [hege s h2] at hp
        rw [hege (s + 1) (by omega)] at hq
        exact hcqg (s + 1) (by omega) (by omega) p q hp hpq hq
  have hgoal := hbase v w e hlet hclosed he0 heN hemono lam heqg
    (by rw [he0, he1, ← hc0]; exact hcomp) (by rw [he0, ← hc0]; exact hiso)
  rw [he0, he1, ← hc0] at hgoal
  exact hgoal


/-! ## Component starts of the joined word -/

/-- **Every component start of the joined word is one of `w` or one of the
chord.**

Below `m` the correspondence is the identity and above it the shift by `m`; the
seam needs no separate case, because a run starting exactly at `m` has `w[m-1]`
before it in the joined word, and that letter not being a `lam`-letter is what
makes `0` a component start of the chord.  A run may straddle the seam, and then
its start is in the `w` half, which is the first case. -/
theorem exists_isCompStart_of_joinWord (_D : RelGenSet G Λ) (lam : Λ) (_v : G)
    {w : List (RelLetter G Λ)} {m : ℕ} {q : List (RelLetter G Λ)}
    (hm : m ≤ w.length) {p : ℕ}
    (hpstart : IsCompStart lam (joinWord w m q) p) :
    (p < m ∧ IsCompStart lam w p) ∨
      (∃ t : ℕ, p = m + t ∧ IsCompStart lam q t) := by
  have hlen : (joinWord w m q).length = m + q.length := length_joinWord w q hm
  obtain ⟨p2, hp2⟩ := hpstart
  have hp12 : p < p2 := hp2.1
  have hp2len : p2 ≤ (joinWord w m q).length := hp2.2.1
  have hprange := hp2.2.2.1
  have hpprev := hp2.2.2.2.1
  have hplen : p < (joinWord w m q).length := by omega
  have hcp := hprange p le_rfl hp12 hplen
  rcases Nat.lt_or_ge p m with hlt | hge
  · -- inside the prefix: the same index of `w`
    refine Or.inl ⟨hlt, ?_⟩
    rw [getElem_joinWord_lt w q hm p hlt hplen (by omega)] at hcp
    obtain ⟨i₀, k₀, hi₀le, hjk₀, hcomp₀⟩ :=
      exists_isComp_of_isCompOf lam w p (by omega) hcp
    have hi₀ : i₀ = p := by
      by_contra hne
      have hp1len : p - 1 < (joinWord w m q).length := by omega
      have hprevw := hcomp₀.2.2.1 (p - 1) (by omega) (by omega) (by omega)
      have hprevn := hpprev (p - 1) (by omega) hp1len
      rw [getElem_joinWord_lt w q hm (p - 1) (by omega) hp1len (by omega)] at hprevn
      exact hprevn hprevw
    exact ⟨k₀, by rw [← hi₀]; exact hcomp₀⟩
  · -- on the chord: the index shifted by `m`
    refine Or.inr ⟨p - m, by omega, ?_⟩
    rw [getElem_joinWord_add w q hm p (p - m) (by omega) hplen (by omega)] at hcp
    obtain ⟨i₀, k₀, hi₀le, hjk₀, hcomp₀⟩ :=
      exists_isComp_of_isCompOf lam q (p - m) (by omega) hcp
    have hi₀ : i₀ = p - m := by
      rcases Nat.eq_zero_or_pos (p - m) with h0 | hpos
      · omega
      · by_contra hne
        have hp1len : p - 1 < (joinWord w m q).length := by omega
        have hprevw := hcomp₀.2.2.1 (p - m - 1) (by omega) (by omega) (by omega)
        have hprevn := hpprev (p - 1) (by omega) hp1len
        rw [getElem_joinWord_add w q hm (p - 1) (p - m - 1) (by omega) hp1len
          (by omega)] at hprevn
        exact hprevn hprevw
    exact ⟨k₀, by rw [← hi₀]; exact hcomp₀⟩

/-- **Isolation transfers to the joined word.**

What has to be added to isolation in `w` is exactly that no component of the
chord is connected to the distinguished one --- which is Case A of Lemma 4.17,
and whose failure is Case B. -/
theorem isIsolated_joinWord (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} {m : ℕ} {q : List (RelLetter G Λ)}
    (hm : m ≤ w.length) {i : ℕ} (hi : i ≤ m)
    (hcompJ : IsCompStart lam (joinWord w m q) i)
    (hiso : IsIsolated D.fam lam v w i)
    (hchord : ∀ t : ℕ, IsCompStart lam q t →
      ¬ Connected D.fam lam v (joinWord w m q) i (m + t)) :
    IsIsolated D.fam lam v (joinWord w m q) i := by
  refine ⟨hcompJ, ?_⟩
  intro p hpi hpstart hconn
  rcases exists_isCompStart_of_joinWord D lam v hm hpstart with ⟨hlt, hstart⟩ | h
  · -- a component of `w`: isolation in `w` forbids the connection
    have hmem : (vertex v (joinWord w m q) i)⁻¹ *
        vertex v (joinWord w m q) p ∈ D.fam lam := hconn
    rw [vertex_joinWord_le v w q hm i hi,
      vertex_joinWord_le v w q hm p (by omega)] at hmem
    exact hiso.2 p hpi hstart hmem
  · -- a component of the chord: excluded by hypothesis
    obtain ⟨t, hpt, hstart⟩ := h
    subst hpt
    exact hchord t hstart hconn

end OsinComponents
end GGT
end GroupApproximation
