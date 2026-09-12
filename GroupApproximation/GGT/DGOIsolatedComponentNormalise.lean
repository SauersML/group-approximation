import GroupApproximation.GGT.DGOIsolatedComponentBridge
import GroupApproximation.GGT.OsinTheorem54SepPolygonVertex
import GroupApproximation.GGT.OsinTheorem54SepFourGonPinning

/-!
# Collapsing a run to the single letter it spans

Dahmani--Guirardel--Osin normalise the distinguished component of a polygon to a
single edge before their Lemma 4.16 construction starts.  This module performs
that surgery on the word:

    normWord w lam i k s = w.take i ++ comp lam s :: w.drop k ,

with `s` the span of the run `[i,k)`.  The run is replaced by one `lam`-letter of
the same value, so the word spells the same element, the component at `i` is a
single letter, its span is *literally the same group element* --- which is why
`d̂_lam` of it is preserved with nothing to prove --- and isolatedness survives.

Concept grep before writing: `take … ++ … :: … drop`, `splice`, `normalis` across
the tree.  The same list surgery appears in `DGOIsolatedComponentReduce`'s
`exists_splice`, which splices between two *connected* components of an avoiding
path and is measured in length, not in sides; nothing there is about a single
run, a polygon, or isolation, and its conclusion is an existential rather than a
named word, so the two do not overlap.  The list and vertex arithmetic is reused:
`listVal_take_split` (SepFourGonPinning), `vertex_append_of_le`,
`vertex_append_add`, `vertex_eq_mul_vertex_one` (SepPolygonVertex),
`vertex_take_eq` (SepFinite), `vertex_drop_eq` (DGOIsolatedComponentBridge).

## What is proved

* `length_normWord`, `letters_normWord`, `listVal_normWord` --- the collapsed word
  is admissible and spells the same element.
* `getElem_normWord_lt`, `getElem_normWord_self`, `getElem_normWord_add` --- its
  letters, in the three ranges.  They are proved through `getElem?`, where the
  index arithmetic is free of dependent proofs, and converted back at the end.
* `vertex_normWord_le`, `vertex_normWord_add` --- its vertices are vertices of
  `w`: those before `i` unchanged, those after the new letter shifted by `k-i-1`.
  The interior vertices of the run are the ones that disappear.
* `isComp_normWord` --- the component at `i` is now the single letter, with the
  same endpoints, hence the same span.
* `exists_isCompStart_of_normWord` --- every component start of the collapsed word
  other than `i` comes from one of `w`, at the same vertex.
* `isIsolated_normWord` --- isolatedness is preserved.  This is the only clause
  with content: it is exactly the previous item plus the vertex identification.

## What the polygon transfer costs, which is not nothing

Collapsing does *not* transport a `(μ,b)`-quasi-geodesic polygon structure at the
same `b`, and the loss is real rather than an artefact of a clumsy cut function.
A corner `j` of the polygon strictly inside the run has nowhere to go: the two
candidate images are the ends of the new letter, whose vertices are `vertex v w i`
and `vertex v w k`, and both differ from `vertex v w j` --- by at most one letter,
since all three lie in one coset of `H lam`, but by at least the amount that the
clause on the far side of `j` was using.  Sending `j` down to `i` keeps the clause
on the near side exactly (the pair `(c s, i)` is a pair of the old side) and loses
one on the far side; sending it up loses one on the near side.  Either way the
collapsed word is a `(μ, b+1)`-quasi-geodesic polygon and not in general a
`(μ,b)`-one.

So a corner strictly inside the run is what the normalisation costs, and when
there is none --- in particular when the run lies inside one side, which is the
case `DGOIsolatedComponentRecut` already handles --- there is nothing to pay and
nothing to collapse.  The `b + 1` is recorded here rather than proved: which
regime the §4.2 argument is run in is a routing decision, and at `(1,0)` the
quadrangle-thinness constant is `2δ` while at `(1,1)` it needs quasi-geodesic
stability, which this repository does not have.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The collapsed word -/

/-- **The word with the run `[i,k)` replaced by one `lam`-letter of value `s`.** -/
def normWord (w : List (RelLetter G Λ)) (lam : Λ) (i k : ℕ) (s : G) :
    List (RelLetter G Λ) :=
  w.take i ++ RelLetter.comp lam s :: w.drop k

omit [Group G] in
/-- The collapsed word has `i + 1 + (|w| - k)` letters. -/
theorem length_normWord (w : List (RelLetter G Λ)) (lam : Λ) (i k : ℕ) (s : G)
    (hi : i ≤ w.length) :
    (normWord w lam i k s).length = i + 1 + (w.length - k) := by
  show (w.take i ++ RelLetter.comp lam s :: w.drop k).length = i + 1 + (w.length - k)
  rw [List.length_append, List.length_take_of_le hi, List.length_cons,
    List.length_drop]
  omega

/-- Every letter of the collapsed word is admissible. -/
theorem letters_normWord (D : RelGenSet G Λ) {w : List (RelLetter G Λ)}
    (hlet : ∀ a ∈ w, D.IsLetter a) (lam : Λ) (i k : ℕ) {s : G}
    (hs : s ∈ D.fam lam) : ∀ a ∈ normWord w lam i k s, D.IsLetter a := by
  intro a ha
  have ha' : a ∈ w.take i ++ RelLetter.comp lam s :: w.drop k := ha
  rcases List.mem_append.mp ha' with hpre | hrest
  · exact hlet a (List.take_subset i w hpre)
  · rcases List.mem_cons.mp hrest with rfl | hsuf
    · exact hs
    · exact hlet a (List.drop_subset k w hsuf)

/-- **The collapsed word spells the same element**, the new letter carrying the
value of the run it replaces. -/
theorem listVal_normWord (w : List (RelLetter G Λ)) (lam : Λ) {i k : ℕ}
    (hik : i ≤ k) :
    RelLetter.listVal
        (normWord w lam i k (RelLetter.listVal ((w.drop i).take (k - i))))
      = RelLetter.listVal w := by
  show RelLetter.listVal (w.take i ++ RelLetter.comp lam
    (RelLetter.listVal ((w.drop i).take (k - i))) :: w.drop k)
      = RelLetter.listVal w
  rw [listVal_append, listVal_cons]
  show RelLetter.listVal (w.take i) *
      (RelLetter.listVal ((w.drop i).take (k - i)) * RelLetter.listVal (w.drop k))
    = RelLetter.listVal w
  rw [← mul_assoc, listVal_take_split w i k hik, ← listVal_append,
    List.take_append_drop]

/-! ## The letters of the collapsed word -/

omit [Group G] in
/-- Before the new letter, the letters are those of `w`. -/
theorem getElem_normWord_lt (w : List (RelLetter G Λ)) (lam : Λ) (i k : ℕ) (s : G)
    (hi : i ≤ w.length) (p : ℕ) (hpi : p < i)
    (hp : p < (normWord w lam i k s).length) (hpw : p < w.length) :
    (normWord w lam i k s)[p]'hp = w[p]'hpw := by
  have h1 : (normWord w lam i k s)[p]? = w[p]? := by
    show (w.take i ++ RelLetter.comp lam s :: w.drop k)[p]? = w[p]?
    rw [List.getElem?_append_left
        (by rw [List.length_take_of_le hi]; exact hpi),
      List.getElem?_take_of_lt hpi]
  rw [List.getElem?_eq_getElem hp, List.getElem?_eq_getElem hpw] at h1
  exact Option.some.inj h1

omit [Group G] in
/-- At `i` the collapsed word has the new letter. -/
theorem getElem_normWord_self (w : List (RelLetter G Λ)) (lam : Λ) (i k : ℕ)
    (s : G) (hi : i ≤ w.length) (p : ℕ) (hpi : p = i)
    (hp : p < (normWord w lam i k s).length) :
    (normWord w lam i k s)[p]'hp = RelLetter.comp lam s := by
  have h1 : (normWord w lam i k s)[p]? = some (RelLetter.comp lam s) := by
    show (w.take i ++ RelLetter.comp lam s :: w.drop k)[p]?
      = some (RelLetter.comp lam s)
    rw [List.getElem?_append_right
        (by rw [List.length_take_of_le hi]; omega),
      List.length_take_of_le hi, show p - i = 0 from by omega,
      List.getElem?_cons_zero]
  rw [List.getElem?_eq_getElem hp] at h1
  exact Option.some.inj h1

omit [Group G] in
/-- After the new letter, the letters are those of `w` from `k` on. -/
theorem getElem_normWord_add (w : List (RelLetter G Λ)) (lam : Λ) (i k : ℕ)
    (s : G) (hi : i ≤ w.length) (p t : ℕ) (hpt : p = i + 1 + t)
    (hp : p < (normWord w lam i k s).length) (hpw : k + t < w.length) :
    (normWord w lam i k s)[p]'hp = w[k + t]'hpw := by
  have h1 : (normWord w lam i k s)[p]? = w[k + t]? := by
    show (w.take i ++ RelLetter.comp lam s :: w.drop k)[p]? = w[k + t]?
    rw [List.getElem?_append_right
        (by rw [List.length_take_of_le hi]; omega),
      List.length_take_of_le hi, show p - i = t + 1 from by omega,
      List.getElem?_cons_succ, List.getElem?_drop]
  rw [List.getElem?_eq_getElem hp, List.getElem?_eq_getElem hpw] at h1
  exact Option.some.inj h1

/-! ## The vertices of the collapsed word -/

/-- Vertices before the new letter are unchanged. -/
theorem vertex_normWord_le (v : G) (w : List (RelLetter G Λ)) (lam : Λ)
    (i k : ℕ) (s : G) (hi : i ≤ w.length) (p : ℕ) (hp : p ≤ i) :
    vertex v (normWord w lam i k s) p = vertex v w p := by
  show vertex v (w.take i ++ RelLetter.comp lam s :: w.drop k) p = vertex v w p
  rw [vertex_append_of_le (w.take i) (RelLetter.comp lam s :: w.drop k) v p
      (by rw [List.length_take_of_le hi]; exact hp),
    vertex_take_eq v w i p hp]

/-- Vertices after the new letter are those of `w` from `k` on: the interior
vertices of the run are the ones the collapse removes. -/
theorem vertex_normWord_add (v : G) (w : List (RelLetter G Λ)) (lam : Λ)
    (i k : ℕ) (s : G) (hi : i ≤ w.length)
    (hspan : vertex v w i * s = vertex v w k) (p t : ℕ) (hpt : p = i + 1 + t) :
    vertex v (normWord w lam i k s) p = vertex v w (k + t) := by
  show vertex v (w.take i ++ RelLetter.comp lam s :: w.drop k) p
      = vertex v w (k + t)
  rw [show p = (w.take i).length + (t + 1) from by
      rw [List.length_take_of_le hi]; omega,
    vertex_append_add (w.take i) (RelLetter.comp lam s :: w.drop k) v (t + 1)]
  show vertex (v * RelLetter.listVal (w.take i) * s) (w.drop k) t
      = vertex v w (k + t)
  rw [← vertex_eq_mul_listVal_take w v i, hspan,
    vertex_eq_mul_vertex_one (w.drop k) (vertex v w k) t, vertex_drop_eq]

/-! ## The component, and its span -/

omit [Group G] in
/-- **The collapsed run is a component of one letter.**  Its endpoints are `i`
and `i + 1`, and by `vertex_normWord_le` and `vertex_normWord_add` its span is
`(vertex v w i)⁻¹ * vertex v w k`, the span of the run it replaces. -/
theorem isComp_normWord (w : List (RelLetter G Λ)) (lam : Λ) {i k : ℕ} (s : G)
    (hcomp : IsComp lam w i k) :
    IsComp lam (normWord w lam i k s) i (i + 1) := by
  have hik : i < k := hcomp.1
  have hkw : k ≤ w.length := hcomp.2.1
  have hprev := hcomp.2.2.2.1
  have hnext := hcomp.2.2.2.2
  have hi : i ≤ w.length := by omega
  have hlen : (normWord w lam i k s).length = i + 1 + (w.length - k) :=
    length_normWord w lam i k s hi
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · intro j hj1 hj2 hjw
    rw [getElem_normWord_self w lam i k s hi j (by omega) hjw]
    exact rfl
  · intro j hj hjw hc
    rw [getElem_normWord_lt w lam i k s hi j (by omega) hjw (by omega)] at hc
    exact hprev j (by omega) (by omega) hc
  · intro hk hc
    rw [getElem_normWord_add w lam i k s hi (i + 1) 0 (by omega) hk
      (by omega)] at hc
    exact hnext (by omega) hc

/-! ## Isolation -/

/-- **Every other component start of the collapsed word comes from one of `w`,
at the same vertex.**

The component starts of `normWord w lam i k s` are: those of `w` below `i`,
unchanged; the new letter at `i`; and those of `w` at or above `k`, shifted down
by `k - i - 1`.  Nothing starts at `i + 1`, because the letter there is `w[k]`,
which is not a `lam`-letter --- the run was maximal. -/
theorem exists_isCompStart_of_normWord (v : G) {w : List (RelLetter G Λ)}
    {lam : Λ} {i k : ℕ} (s : G) (hcomp : IsComp lam w i k)
    (hspan : vertex v w i * s = vertex v w k) {j : ℕ}
    (hjstart : IsCompStart lam (normWord w lam i k s) j) (hji : j ≠ i) :
    ∃ p : ℕ, IsCompStart lam w p ∧ p ≠ i ∧
      vertex v (normWord w lam i k s) j = vertex v w p := by
  have hik : i < k := hcomp.1
  have hkw : k ≤ w.length := hcomp.2.1
  have hnext := hcomp.2.2.2.2
  have hi : i ≤ w.length := by omega
  have hlen : (normWord w lam i k s).length = i + 1 + (w.length - k) :=
    length_normWord w lam i k s hi
  obtain ⟨j2, hj2⟩ := hjstart
  have hj12 : j < j2 := hj2.1
  have hj2len : j2 ≤ (normWord w lam i k s).length := hj2.2.1
  have hjrange := hj2.2.2.1
  have hjprev := hj2.2.2.2.1
  have hjlen : j < (normWord w lam i k s).length := by omega
  have hcj := hjrange j le_rfl hj12 hjlen
  rcases Nat.lt_or_ge j i with hlt | hge
  · -- below the new letter: the same index of `w`
    rw [getElem_normWord_lt w lam i k s hi j hlt hjlen (by omega)] at hcj
    obtain ⟨i₀, k₀, hi₀le, hjk₀, hcomp₀⟩ :=
      exists_isComp_of_isCompOf lam w j (by omega) hcj
    have hi₀ : i₀ = j := by
      by_contra hne
      have hj1len : j - 1 < (normWord w lam i k s).length := by omega
      have hprevw := hcomp₀.2.2.1 (j - 1) (by omega) (by omega) (by omega)
      have hprevn := hjprev (j - 1) (by omega) hj1len
      rw [getElem_normWord_lt w lam i k s hi (j - 1) (by omega) hj1len
        (by omega)] at hprevn
      exact hprevn hprevw
    refine ⟨j, ⟨k₀, ?_⟩, by omega, ?_⟩
    · rw [← hi₀]
      exact hcomp₀
    · exact vertex_normWord_le v w lam i k s hi j (by omega)
  · -- above the new letter: shifted by `k - i - 1`
    have hkw' : k < w.length := by omega
    have hj1 : i + 2 ≤ j := by
      rcases Nat.lt_or_ge j (i + 2) with hj | hj
      · exfalso
        have hji1 : j = i + 1 := by omega
        rw [getElem_normWord_add w lam i k s hi j 0 (by omega) hjlen
          (by omega)] at hcj
        exact hnext (by omega) hcj
      · exact hj
    have ht : j = i + 1 + (j - i - 1) := by omega
    rw [getElem_normWord_add w lam i k s hi j (j - i - 1) ht hjlen
      (by omega)] at hcj
    obtain ⟨i₀, k₀, hi₀le, hjk₀, hcomp₀⟩ :=
      exists_isComp_of_isCompOf lam w (k + (j - i - 1)) (by omega) hcj
    have hi₀ : i₀ = k + (j - i - 1) := by
      by_contra hne
      have hj1len : j - 1 < (normWord w lam i k s).length := by omega
      have hprevw := hcomp₀.2.2.1 (k + (j - i - 2)) (by omega) (by omega)
        (by omega)
      have hprevn := hjprev (j - 1) (by omega) hj1len
      rw [getElem_normWord_add w lam i k s hi (j - 1) (j - i - 2) (by omega)
        hj1len (by omega)] at hprevn
      exact hprevn hprevw
    refine ⟨k + (j - i - 1), ⟨k₀, ?_⟩, by omega, ?_⟩
    · rw [← hi₀]
      exact hcomp₀
    · exact vertex_normWord_add v w lam i k s hi hspan j (j - i - 1) ht

/-- **Collapsing preserves isolatedness.**

An isolated component stays isolated: every other component start of the
collapsed word is one of `w` at the same vertex, so a connection in the collapsed
word is a connection in `w`, which isolatedness forbids. -/
theorem isIsolated_normWord (D : RelGenSet G Λ) {lam : Λ} (v : G)
    {w : List (RelLetter G Λ)} {i k : ℕ} (s : G) (hcomp : IsComp lam w i k)
    (hspan : vertex v w i * s = vertex v w k)
    (hiso : IsIsolated D.fam lam v w i) :
    IsIsolated D.fam lam v (normWord w lam i k s) i := by
  have hik : i < k := hcomp.1
  have hkw : k ≤ w.length := hcomp.2.1
  have hi : i ≤ w.length := by omega
  refine ⟨⟨i + 1, isComp_normWord w lam s hcomp⟩, ?_⟩
  intro j hji hjstart hconn
  obtain ⟨p, hpstart, hpi, hvp⟩ :=
    exists_isCompStart_of_normWord v s hcomp hspan hjstart hji
  refine hiso.2 p hpi hpstart ?_
  have hmem : (vertex v (normWord w lam i k s) i)⁻¹ *
      vertex v (normWord w lam i k s) j ∈ D.fam lam := hconn
  rw [vertex_normWord_le v w lam i k s hi i le_rfl, hvp] at hmem
  exact hmem

end OsinComponents
end GGT
end GroupApproximation
