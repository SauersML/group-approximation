import GroupApproximation.GGT.DGOAssemblyVertices

/-!
# The letters of the halves

`GGT/DGOAssemblyVertices.lean` says where the halves' *vertices* come from; this
says where their *letters* come from.  The two together are what the isolation
argument needs, since a component is a run of letters read at a vertex, and
neither half of that dictionary is usable without the other.

Each half is a concatenation, so each has one lemma per region:

    firstHalf  = arcWord ++ revWord t          arc region, chord region
    secondHalf = (w.drop (c b) ++ w.take (c a)) ++ t
                                               two arc regions, chord region

## Indices are stated forwards

The natural statement of a chord-region lemma is about `(firstHalf …)[i]` for
`c b − c a ≤ i`, and its right-hand side then reads `(revWord t)[i − (c b − c a)]`
--- a subtraction *inside* a dependent `getElem` index, which neither `rw` nor
`congr` handles cleanly.  Every lemma here is therefore stated at
`(c b − c a) + j` with `j` free, so the index on the left is a sum and the index
on the right is a variable, and no rewriting inside an index is ever needed.
That is the same discipline as `DGOCycleSplice.getElem_splice_mid`, which pays
for the subtraction once with a `congr 1`; stating forwards avoids paying at
all.

## Why these are group-free

None of it touches the group: `RelLetter G Λ` needs no `Group G` instance and
these are statements about `take`, `drop` and `++`.  So the lemmas about
`arcWord` and `secondHalf` carry `omit [Group G] in`, while those about
`firstHalf` do not --- `firstHalf` goes through `revWord`, hence `invLetter`,
hence a group inverse, so it binds the instance and its lemmas use it.
-/

namespace GroupApproximation
namespace GGT
namespace DGOPolygonCut

open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The arc -/

omit [Group G] in
/-- **A letter of the arc is a letter of the polygon.** -/
theorem getElem_arcWord (w : List (RelLetter G Λ)) (c : ℕ → ℕ) {a b i : ℕ}
    (hb : c b ≤ w.length) (hi : i < c b - c a)
    (h' : i < (arcWord w c a b).length) :
    (arcWord w c a b)[i]'h' = w[c a + i]'(by omega) := by
  show ((w.drop (c a)).take (c b - c a))[i]'h' = w[c a + i]'(by omega)
  simp

/-! ## The first half -/

/-- **A letter of the first half, along the arc.** -/
theorem getElem_firstHalf_arc (w : List (RelLetter G Λ)) (c : ℕ → ℕ) {a b i : ℕ}
    (hb : c b ≤ w.length) (hi : i < c b - c a) (t : List (RelLetter G Λ))
    (h' : i < (firstHalf w c a b t).length) :
    (firstHalf w c a b t)[i]'h' = w[c a + i]'(by omega) := by
  have hlen : i < (arcWord w c a b).length := by
    rw [length_arcWord w c hb]
    exact hi
  show (arcWord w c a b ++ revWord t)[i]'h' = w[c a + i]'(by omega)
  rw [List.getElem_append_left hlen]
  exact getElem_arcWord w c hb hi hlen

/-- **A letter of the first half, along the chord.** -/
theorem getElem_firstHalf_chord (w : List (RelLetter G Λ)) (c : ℕ → ℕ)
    {a b j : ℕ} (hb : c b ≤ w.length) (t : List (RelLetter G Λ))
    (hj : j < t.length)
    (h' : (c b - c a) + j < (firstHalf w c a b t).length) :
    (firstHalf w c a b t)[(c b - c a) + j]'h'
      = (revWord t)[j]'(by rw [length_revWord]; exact hj) := by
  have harc : (arcWord w c a b).length = c b - c a := length_arcWord w c hb
  have hlen : (arcWord w c a b).length ≤ (c b - c a) + j := by omega
  show (arcWord w c a b ++ revWord t)[(c b - c a) + j]'h' = _
  rw [List.getElem_append_right hlen]
  simp [harc]

/-! ## The second half -/

omit [Group G] in
/-- **A letter of the second half, along the arc that starts at corner `b`.** -/
theorem getElem_secondHalf_drop (w : List (RelLetter G Λ)) (c : ℕ → ℕ)
    {a b i : ℕ} (hi : i < w.length - c b) (t : List (RelLetter G Λ))
    (h' : i < (secondHalf w c a b t).length) :
    (secondHalf w c a b t)[i]'h' = w[c b + i]'(by omega) := by
  have hlen : i < (w.drop (c b)).length := by
    rw [List.length_drop]
    exact hi
  have hlen' : i < (w.drop (c b) ++ w.take (c a)).length := by
    rw [List.length_append]
    omega
  show (w.drop (c b) ++ w.take (c a) ++ t)[i]'h' = w[c b + i]'(by omega)
  rw [List.getElem_append_left hlen', List.getElem_append_left hlen]
  simp

omit [Group G] in
/-- **A letter of the second half, along the arc that ends at corner `a`.**

This is the region where the second half has wrapped past the end of the word
and is reading the polygon again from its basepoint. -/
theorem getElem_secondHalf_take (w : List (RelLetter G Λ)) (c : ℕ → ℕ)
    {a b i : ℕ} (hi : i < c a) (ha : c a ≤ w.length)
    (t : List (RelLetter G Λ))
    (h' : (w.length - c b) + i < (secondHalf w c a b t).length) :
    (secondHalf w c a b t)[(w.length - c b) + i]'h' = w[i]'(by omega) := by
  have hdroplen : (w.drop (c b)).length = w.length - c b := by
    rw [List.length_drop]
  have htakelen : (w.take (c a)).length = c a := by
    rw [List.length_take]
    omega
  have hge : (w.drop (c b)).length ≤ (w.length - c b) + i := by omega
  have hlt : (w.length - c b) + i < (w.drop (c b) ++ w.take (c a)).length := by
    rw [List.length_append]
    omega
  show (w.drop (c b) ++ w.take (c a) ++ t)[(w.length - c b) + i]'h' = w[i]'(by omega)
  rw [List.getElem_append_left hlt, List.getElem_append_right hge]
  simp [hdroplen]

omit [Group G] in
/-- **A letter of the second half, along the chord.** -/
theorem getElem_secondHalf_chord (w : List (RelLetter G Λ)) (c : ℕ → ℕ)
    {a b j : ℕ} (ha : c a ≤ w.length)
    (t : List (RelLetter G Λ)) (hj : j < t.length)
    (h' : (w.length - c b) + c a + j < (secondHalf w c a b t).length) :
    (secondHalf w c a b t)[(w.length - c b) + c a + j]'h' = t[j]'hj := by
  have hdroplen : (w.drop (c b)).length = w.length - c b := by
    rw [List.length_drop]
  have htakelen : (w.take (c a)).length = c a := by
    rw [List.length_take]
    omega
  have hpre : (w.drop (c b) ++ w.take (c a)).length = (w.length - c b) + c a := by
    rw [List.length_append, hdroplen, htakelen]
  have hge : (w.drop (c b) ++ w.take (c a)).length
      ≤ (w.length - c b) + c a + j := by omega
  show (w.drop (c b) ++ w.take (c a) ++ t)[(w.length - c b) + c a + j]'h' = t[j]'hj
  rw [List.getElem_append_right hge]
  simp [hpre]

omit [Group G] in
omit [Group G] in
/-- **A letter anywhere on the wrapped second-half arc is the corresponding
letter of the rotated polygon.** -/
theorem getElem_secondHalf_rotWord (w : List (RelLetter G Λ)) (c : ℕ → ℕ)
    {a b i : ℕ} (ha : c a ≤ c b) (hb : c b ≤ w.length)
    (hi : i < (w.length - c b) + c a) (t : List (RelLetter G Λ))
    (h' : i < (secondHalf w c a b t).length) :
    (secondHalf w c a b t)[i]'h' =
      (rotWord w (c b))[i]'(by
        rw [length_rotWord w hb]
        omega) := by
  rw [List.getElem_of_eq (secondHalf_eq_rotWord_append w c ha hb t) h']
  have hrot : (rotWord w (c b)).length = w.length := length_rotWord w hb
  have hprefix : ((rotWord w (c b)).take ((w.length - c b) + c a)).length =
      (w.length - c b) + c a := by
    rw [List.length_take, hrot]
    omega
  rw [List.getElem_append_left (by rw [hprefix]; exact hi)]
  simp

/-! ## What a letter is, transfers -/

/-- **Being a `lam`-letter transfers along the arc of the first half.**

The corollary the isolation argument consumes: component structure along the arc
is component structure of the polygon, because the letters are the same
letters. -/
theorem isCompOf_firstHalf_arc_iff (lam : Λ) (w : List (RelLetter G Λ))
    (c : ℕ → ℕ) {a b i : ℕ} (hb : c b ≤ w.length) (hi : i < c b - c a)
    (t : List (RelLetter G Λ)) (h' : i < (firstHalf w c a b t).length) :
    ((firstHalf w c a b t)[i]'h').IsCompOf lam
      ↔ (w[c a + i]'(by omega)).IsCompOf lam := by
  rw [getElem_firstHalf_arc w c hb hi t h']

omit [Group G] in
/-- **Being a `lam`-letter transfers along the first arc of the second half.** -/
theorem isCompOf_secondHalf_drop_iff (lam : Λ) (w : List (RelLetter G Λ))
    (c : ℕ → ℕ) {a b i : ℕ} (hi : i < w.length - c b) (t : List (RelLetter G Λ))
    (h' : i < (secondHalf w c a b t).length) :
    ((secondHalf w c a b t)[i]'h').IsCompOf lam
      ↔ (w[c b + i]'(by omega)).IsCompOf lam := by
  rw [getElem_secondHalf_drop w c hi t h']

omit [Group G] in
/-- **Being a `lam`-letter transfers across the entire wrapped arc through its
rotation model.** -/
theorem isCompOf_secondHalf_rotWord_iff (lam : Λ)
    (w : List (RelLetter G Λ)) (c : ℕ → ℕ) {a b i : ℕ}
    (ha : c a ≤ c b) (hb : c b ≤ w.length)
    (hi : i < (w.length - c b) + c a) (t : List (RelLetter G Λ))
    (h' : i < (secondHalf w c a b t).length) :
    ((secondHalf w c a b t)[i]'h').IsCompOf lam ↔
      ((rotWord w (c b))[i]'(by rw [length_rotWord w hb]; omega)).IsCompOf lam := by
  rw [getElem_secondHalf_rotWord w c ha hb hi t h']

end DGOPolygonCut
end GGT
end GroupApproximation
