import GroupApproximation.GGT.OsinTheorem54SepSegmentComp

/-!
# The vertices of a segment are the vertices of the word, shifted

The last piece of bookkeeping Lemma 5.9 needs.  `isGeodesicWord_segment` makes
the segment a geodesic and `isComp_of_isComp_segment` carries its components to
the word; what is still missing is that the two agree on VERTICES, so that a
component's span is literally the same element on both sides and essential
penetration transfers with no estimate.

`take_take_of_le` is proved here because `Init` has no `take_take` at this
revision --- the same gap `listVal_take_split` was written around.

Unconditional.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **Nested prefixes.**  `Init` has no `take_take` at this revision. -/
theorem take_take_of_le {α : Type*} :
    ∀ (l : List α) (m a : ℕ), a ≤ m → (l.take m).take a = l.take a := by
  intro l
  induction l with
  | nil => intro m a _; simp
  | cons x t ih =>
      intro m a ha
      cases a with
      | zero => simp
      | succ a' =>
          cases m with
          | zero => exact absurd ha (by omega)
          | succ m' =>
              have ha' : a' ≤ m' := by omega
              simp only [List.take_succ_cons]
              rw [ih m' a' ha']

omit [Group G] in
/-- **The length of a segment**, for the side conditions below. -/
theorem length_segment (w : List (RelLetter G Λ)) (k m : ℕ)
    (hkm : k + m ≤ w.length) : ((w.drop k).take m).length = m := by
  rw [List.length_take, List.length_drop]
  omega

/-- **A vertex of a segment is a vertex of the word, at the shifted index.** -/
theorem vertex_segment (w : List (RelLetter G Λ)) (f : G) (k m a : ℕ)
    (ha : a ≤ m) :
    vertex (vertex f w k) ((w.drop k).take m) a = vertex f w (k + a) := by
  have hsub : k + a - k = a := by omega
  have hsplit := listVal_take_split w k (k + a) (by omega)
  rw [hsub] at hsplit
  rw [vertex_eq_mul_listVal_take ((w.drop k).take m) (vertex f w k) a,
    take_take_of_le (w.drop k) m a ha,
    vertex_eq_mul_listVal_take w f k, vertex_eq_mul_listVal_take w f (k + a),
    mul_assoc, hsplit]

/-- **The span of a component of a segment is the span of its image in the
word.**  So essential penetration transfers with no estimate at all. -/
theorem span_segment (w : List (RelLetter G Λ)) (f : G) (k m a b : ℕ)
    (ha : a ≤ m) (hb : b ≤ m) :
    (vertex (vertex f w k) ((w.drop k).take m) a)⁻¹ *
        vertex (vertex f w k) ((w.drop k).take m) b
      = (vertex f w (k + a))⁻¹ * vertex f w (k + b) := by
  rw [vertex_segment w f k m a ha, vertex_segment w f k m b hb]

end OsinComponents
end GGT
end GroupApproximation
