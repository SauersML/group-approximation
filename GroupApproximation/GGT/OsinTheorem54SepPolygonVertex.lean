import GroupApproximation.GGT.OsinTheorem54SepReversal
import GroupApproximation.GGT.OsinTheorem54SepSplit

/-!
# Vertices of a concatenated path, and of a reversed one

A geodesic polygon is one word, and its sides are segments of that word.  To
say anything about a side one has to be able to read the vertices of the
concatenation off the vertices of the pieces, and --- since one side of a
polygon is traversed backwards --- off the vertices of a *reversed* piece.

* `vertex_append_of_le` and `vertex_append_add`: a vertex of `a ++ b` in the
  first block is the corresponding vertex of `a`; one in the second block is
  the corresponding vertex of `b`, read from the endpoint of `a`.
* `vertex_revWord`: the vertex of `revWord s` at index `|s| - j` is the vertex
  of `s` at index `j`, translated by `(listVal s)⁻¹`.  The index reversal is
  exactly `j ↦ |s| - j`, and no hypothesis `j ≤ |s|` is needed: both sides
  saturate at `j = |s|`.
* `length_fourGon`: the length of `p ++ q ++ r ++ revWord s`, which is what the
  index arithmetic of a quadrilateral runs on.

Nothing here is about hyperbolicity, admissibility or components; it is the
bookkeeping those arguments stand on.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A vertex read from `v` is `v` times the vertex read from `1`.** -/
theorem vertex_eq_mul_vertex_one (w : List (RelLetter G Λ)) (v : G) (i : ℕ) :
    vertex v w i = v * vertex (1 : G) w i := by
  rw [vertex_eq_mul_listVal_take w v i, vertex_eq_mul_listVal_take w 1 i,
    one_mul]

/-- **A vertex of `a ++ b` inside the first block is a vertex of `a`.** -/
theorem vertex_append_of_le : ∀ (a b : List (RelLetter G Λ)) (v : G) (i : ℕ),
    i ≤ a.length → vertex v (a ++ b) i = vertex v a i := by
  intro a
  induction a with
  | nil =>
      intro b v i hi
      rw [List.length_nil] at hi
      have hi0 : i = 0 := by omega
      subst hi0
      rw [vertex_zero, vertex_zero]
  | cons x t ih =>
      intro b v i hi
      cases i with
      | zero => rw [vertex_zero, vertex_zero]
      | succ i' =>
          rw [List.length_cons] at hi
          have hi' : i' ≤ t.length := by omega
          rw [List.cons_append, vertex_cons_succ, vertex_cons_succ]
          exact ih b (v * x.val) i' hi'

/-- **A vertex of `a ++ b` in the second block is a vertex of `b`**, read from
the endpoint of `a`. -/
theorem vertex_append_add : ∀ (a b : List (RelLetter G Λ)) (v : G) (k : ℕ),
    vertex v (a ++ b) (a.length + k)
      = vertex (v * RelLetter.listVal a) b k := by
  intro a
  induction a with
  | nil =>
      intro b v k
      rw [List.nil_append, List.length_nil, Nat.zero_add, RelLetter.listVal_nil,
        mul_one]
  | cons x t ih =>
      intro b v k
      have hlen : (x :: t).length + k = (t.length + k) + 1 := by
        rw [List.length_cons]
        omega
      rw [hlen, List.cons_append, vertex_cons_succ, ih b (v * x.val) k,
        listVal_cons, mul_assoc]

/-- **Reversal turns a concatenation around.** -/
theorem revWord_append (w₁ w₂ : List (RelLetter G Λ)) :
    revWord (w₁ ++ w₂) = revWord w₂ ++ revWord w₁ := by
  show ((w₁ ++ w₂).map invLetter).reverse
    = (w₂.map invLetter).reverse ++ (w₁.map invLetter).reverse
  rw [List.map_append, List.reverse_append]

/-- **The vertices of a reversed word are the vertices of the word, in the
reverse order and translated.**

Reading `revWord s` for `|s| - j` letters undoes the last `|s| - j` letters of
`s`, so it lands on the vertex of `s` at index `j`, moved by `(listVal s)⁻¹`
because the reversed word is read from the far end.  There is no hypothesis on
`j`: for `j ≥ |s|` both sides are `v`, truncated subtraction and
`vertex _ _ |s| = listVal s` agreeing. -/
theorem vertex_revWord (s : List (RelLetter G Λ)) (v : G) (j : ℕ) :
    vertex v (revWord s) (s.length - j)
      = v * (RelLetter.listVal s)⁻¹ * vertex (1 : G) s j := by
  have hrev : revWord (s.drop j) ++ revWord (s.take j) = revWord s := by
    rw [← revWord_append, List.take_append_drop]
  have hlen : (revWord (s.drop j)).length = s.length - j := by
    rw [length_revWord, List.length_drop]
  have htake : (revWord s).take (s.length - j) = revWord (s.drop j) := by
    rw [← hrev]
    exact List.take_left' hlen
  have hval : RelLetter.listVal (s.take j) * RelLetter.listVal (s.drop j)
      = RelLetter.listVal s := by
    rw [← listVal_append, List.take_append_drop]
  have hvj : vertex (1 : G) s j = RelLetter.listVal (s.take j) := by
    rw [vertex_eq_mul_listVal_take s 1 j, one_mul]
  rw [vertex_eq_mul_listVal_take (revWord s) v (s.length - j), htake,
    listVal_revWord, hvj, ← hval]
  group

/-- **The length of a quadrilateral** whose fourth side is traversed
backwards. -/
theorem length_fourGon (p q r s : List (RelLetter G Λ)) :
    (p ++ q ++ r ++ revWord s).length
      = p.length + q.length + r.length + s.length := by
  rw [List.length_append, List.length_append, List.length_append,
    length_revWord]

end OsinComponents
end GGT
end GroupApproximation
