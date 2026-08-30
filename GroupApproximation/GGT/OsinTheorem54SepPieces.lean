import GroupApproximation.GGT.OsinTheorem54SepPolygon
import GroupApproximation.GGT.OsinTheorem54SepPolygonVertex
import GroupApproximation.GGT.OsinTheorem54SepSmul

/-!
# A chain of geodesic pieces is a quasi-geodesic polygon

The tree builds polygons one shape at a time --- the four-gon, the triangle as a
four-gon with an empty side --- and every one of them exhibits its cut function
by hand.  Osin's Lemma 5.8 needs a polygon whose side count is the length of a
word, so the sides cannot be listed: they have to be assembled.

This module does that once and generically.  Given pieces `ps` --- a list of
words, each geodesic from wherever it is read --- their concatenation is a
`(1,0)`-quasi-geodesic polygon with one side per piece, provided it closes up.
Nothing here knows about `Z`, about the enlargement, or about components.

## The cut function

`pieceCut ps s` is the total length of the first `s` pieces, defined by
recursion rather than as `((ps.map length).take s).sum`: the three facts the
polygon wants --- `0` at `0`, `ps.flatten.length` at `ps.length`, and
monotonicity --- are then one induction each, and the side bound is an induction
over the same recursion.

## Why the pieces are quantified over their basepoint

`hgeo` asks each piece to be geodesic from EVERY `u`, not from one.  That is not
a stronger hypothesis --- `isGeodesicWord_mul_left` says being geodesic is
invariant under left translation, so a piece geodesic at one point is geodesic
at all of them --- and it removes the bookkeeping that would otherwise track
which vertex each piece starts at through the induction.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The cut function -/

/-- **The total length of the first `s` pieces.** -/
def pieceCut : List (List (RelLetter G Λ)) → ℕ → ℕ
  | _, 0 => 0
  | [], _ + 1 => 0
  | q :: qs, s + 1 => q.length + pieceCut qs s

@[simp] theorem pieceCut_zero (ps : List (List (RelLetter G Λ))) :
    pieceCut ps 0 = 0 := by
  cases ps <;> rfl

@[simp] theorem pieceCut_nil (s : ℕ) :
    pieceCut ([] : List (List (RelLetter G Λ))) s = 0 := by
  cases s <;> rfl

@[simp] theorem pieceCut_cons_succ (q : List (RelLetter G Λ))
    (qs : List (List (RelLetter G Λ))) (s : ℕ) :
    pieceCut (q :: qs) (s + 1) = q.length + pieceCut qs s := rfl

theorem pieceCut_mono (ps : List (List (RelLetter G Λ))) (s : ℕ) :
    pieceCut ps s ≤ pieceCut ps (s + 1) := by
  induction ps generalizing s with
  | nil => simp
  | cons q qs ih =>
      cases s with
      | zero => simp
      | succ s' =>
          rw [pieceCut_cons_succ, pieceCut_cons_succ]
          exact Nat.add_le_add_left (ih s') _

theorem pieceCut_length (ps : List (List (RelLetter G Λ))) :
    pieceCut ps ps.length = ps.flatten.length := by
  induction ps with
  | nil => rfl
  | cons q qs ih =>
      rw [List.length_cons, pieceCut_cons_succ, ih, List.flatten_cons,
        List.length_append]

/-! ## Vertices of a concatenation of pieces -/

theorem vertex_flatten_cons_le (v : G) (q : List (RelLetter G Λ))
    (qs : List (List (RelLetter G Λ))) (i : ℕ) (hi : i ≤ q.length) :
    vertex v (q :: qs).flatten i = vertex v q i := by
  rw [List.flatten_cons]
  exact vertex_append_of_le q qs.flatten v i hi

theorem vertex_flatten_cons_add (v : G) (q : List (RelLetter G Λ))
    (qs : List (List (RelLetter G Λ))) (k : ℕ) :
    vertex v (q :: qs).flatten (q.length + k)
      = vertex (v * RelLetter.listVal q) qs.flatten k := by
  rw [List.flatten_cons]
  exact vertex_append_add q qs.flatten v k

/-! ## The side bound -/

/-- **Every side of the concatenation is geodesic.**  The `s`-th side is the
`s`-th piece, read from wherever the earlier pieces left off. -/
theorem sub_le_wordDist_vertex_flatten (D : RelGenSet G Λ) :
    ∀ (ps : List (List (RelLetter G Λ))) (v : G),
      (∀ q ∈ ps, ∀ u : G, IsGeodesicWord D u (u * RelLetter.listVal q) q) →
      ∀ (s : ℕ), s < ps.length → ∀ i j : ℕ, pieceCut ps s ≤ i → i ≤ j →
        j ≤ pieceCut ps (s + 1) →
        j - i ≤ wordDist D.alphabet.carrier (vertex v ps.flatten i)
          (vertex v ps.flatten j) := by
  intro ps
  induction ps with
  | nil =>
      intro v _ s hs
      simp at hs
  | cons q qs ih =>
      intro v hgeo s hs i j hi hij hj
      cases s with
      | zero =>
          rw [pieceCut_zero] at hi
          rw [pieceCut_cons_succ, pieceCut_zero, Nat.add_zero] at hj
          rw [vertex_flatten_cons_le v q qs i (by omega),
            vertex_flatten_cons_le v q qs j hj]
          exact sub_le_wordDist_vertex D (hgeo q List.mem_cons_self v) i j hij hj
      | succ s' =>
          rw [pieceCut_cons_succ] at hi
          rw [pieceCut_cons_succ] at hj
          obtain ⟨i', rfl⟩ : ∃ i', i = q.length + i' := ⟨i - q.length, by omega⟩
          obtain ⟨j', rfl⟩ : ∃ j', j = q.length + j' := ⟨j - q.length, by omega⟩
          have hs' : s' < qs.length := by
            rw [List.length_cons] at hs
            omega
          have hrec := ih (v * RelLetter.listVal q)
            (fun r hr u => hgeo r (List.mem_cons_of_mem q hr) u) s' hs' i' j'
            (by omega) (by omega) (by omega)
          rw [vertex_flatten_cons_add, vertex_flatten_cons_add]
          have hsub : q.length + j' - (q.length + i') = j' - i' := by omega
          rw [hsub]
          exact hrec

/-! ## The polygon -/

/-- **A closed chain of geodesic pieces is a `(1,0)`-quasi-geodesic polygon**,
with one side per piece. -/
theorem isQuasiGeodesicPolygon_flatten (D : RelGenSet G Λ) (v : G)
    (ps : List (List (RelLetter G Λ)))
    (hgeo : ∀ q ∈ ps, ∀ u : G, IsGeodesicWord D u (u * RelLetter.listVal q) q)
    (hclosed : RelLetter.listVal ps.flatten = 1) :
    IsQuasiGeodesicPolygon D 1 0 ps.length v ps.flatten := by
  refine ⟨?_, hclosed, pieceCut ps, pieceCut_zero ps, pieceCut_length ps,
    pieceCut_mono ps, ?_⟩
  · intro a ha
    obtain ⟨q, hq, haq⟩ := List.mem_flatten.mp ha
    exact (hgeo q hq v).1 a haq
  · intro s hs i j hi hij hj
    have hnat := sub_le_wordDist_vertex_flatten D ps v hgeo s hs i j hi hij hj
    rw [div_one, sub_zero]
    exact_mod_cast hnat

end OsinComponents
end GGT
end GroupApproximation
