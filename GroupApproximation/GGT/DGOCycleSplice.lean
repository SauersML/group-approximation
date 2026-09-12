import GroupApproximation.GGT.DGOShortIsolatingCycle

/-!
# Splicing a connector into a closed word

Every cycle Dahmani--Guirardel--Osin's Lemma 4.16 builds has the same shape: a
prefix of the polygon, a connector, and a suffix of the polygon,

    q = w.take m ++ (r ++ w.drop j) ,

with the connector `r` running from `vertex v w m` to `vertex v w j`.  The four
cases of their Case 4 differ only in which `m` and `j` are chosen and how the
connector is produced; the bookkeeping below is shared by all of them, and by
the two-connector case as well, applied twice.

`vertex_splice` reads off the vertices of `q` in the three ranges --- prefix,
connector, suffix --- and `getElem_splice_left`, `_mid` and `_right` do the same
for the letters.  Those six facts are what turn `IsIsolated` for `q`, through
`isIsolated_zero_of_notMem`, into two obligations that are already discharged:
polygon vertices by `notMem_coset_of_isIsolated_zero`, connector vertices by
`notMem_coset_vertex_of_offset`.

The suffix identity is where closedness of the polygon is used, through
`vertex_drop_eq`: reading `w.drop j` from `vertex v w j` continues along `w`.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Vertices of a splice -/

/-- **The vertices of `w.take m ++ (r ++ w.drop j)`**, in the three ranges. -/
theorem vertex_splice (v : G) (w r : List (RelLetter G Λ)) {m j : ℕ}
    (hm : m ≤ w.length)
    (hr : RelLetter.listVal r = (vertex v w m)⁻¹ * vertex v w j) :
    (∀ i : ℕ, i ≤ m →
        vertex v (w.take m ++ (r ++ w.drop j)) i = vertex v w i) ∧
      (∀ t : ℕ, t ≤ r.length →
        vertex v (w.take m ++ (r ++ w.drop j)) (m + t)
          = vertex (vertex v w m) r t) ∧
      (∀ t : ℕ, vertex v (w.take m ++ (r ++ w.drop j)) (m + r.length + t)
          = vertex v w (j + t)) := by
  have hlenm : (w.take m).length = m := by
    rw [List.length_take]
    omega
  have hvm : v * RelLetter.listVal (w.take m) = vertex v w m :=
    (vertex_eq_mul_listVal_take w v m).symm
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [vertex_append_of_le (w.take m) (r ++ w.drop j) v i (by omega)]
    exact vertex_take_eq v w m i hi
  · intro t ht
    have hidx : m + t = (w.take m).length + t := by rw [hlenm]
    rw [hidx, vertex_append_add, hvm]
    exact vertex_append_of_le r (w.drop j) (vertex v w m) t ht
  · intro t
    have hidx : m + r.length + t = (w.take m).length + (r.length + t) := by
      rw [hlenm]
      omega
    have hval : vertex v w m * RelLetter.listVal r = vertex v w j := by
      rw [hr]
      group
    rw [hidx, vertex_append_add, hvm, vertex_append_add, hval,
      vertex_eq_mul_vertex_one (w.drop j) (vertex v w j) t]
    exact vertex_drop_eq w v j t

/-! ## Letters of a splice -/

omit [Group G] in
/-- **A letter of the prefix.** -/
theorem getElem_splice_left (w r : List (RelLetter G Λ)) {m j i : ℕ}
    (hm : m ≤ w.length) (hi : i < m)
    (h' : i < (w.take m ++ (r ++ w.drop j)).length) :
    (w.take m ++ (r ++ w.drop j))[i]'h' = w[i]'(by omega) := by
  have hlenm : (w.take m).length = m := by
    rw [List.length_take]
    omega
  rw [List.getElem_append_left (by omega : i < (w.take m).length)]
  simp

omit [Group G] in
/-- **A letter of the connector.** -/
theorem getElem_splice_mid (w r : List (RelLetter G Λ)) {m j i : ℕ}
    (hm : m ≤ i) (hi : i < m + r.length) (hmw : m ≤ w.length)
    (h' : i < (w.take m ++ (r ++ w.drop j)).length) :
    (w.take m ++ (r ++ w.drop j))[i]'h' = r[i - m]'(by omega) := by
  have hlenm : (w.take m).length = m := by
    rw [List.length_take]
    omega
  rw [List.getElem_append_right (by omega : (w.take m).length ≤ i),
    List.getElem_append_left (by omega : i - (w.take m).length < r.length)]
  congr 1
  omega

omit [Group G] in
/-- **A letter of the suffix.** -/
theorem getElem_splice_right (w r : List (RelLetter G Λ)) {m j i : ℕ}
    (hm : m + r.length ≤ i) (hmw : m ≤ w.length)
    (h' : i < (w.take m ++ (r ++ w.drop j)).length) :
    (w.take m ++ (r ++ w.drop j))[i]'h'
      = w[j + (i - m - r.length)]'(by
          rw [List.length_append, List.length_append, List.length_take,
            List.length_drop] at h'
          omega) := by
  have hlenm : (w.take m).length = m := by
    rw [List.length_take]
    omega
  rw [List.getElem_append_right (by omega : (w.take m).length ≤ i),
    List.getElem_append_right (by omega : r.length ≤ i - (w.take m).length),
    List.getElem_drop]
  congr 1
  omega

end OsinComponents
end GGT
end GroupApproximation
