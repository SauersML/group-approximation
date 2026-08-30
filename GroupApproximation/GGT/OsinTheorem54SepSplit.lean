import GroupApproximation.GGT.OsinTheorem54SeparatingCosets

/-!
# Cutting an avoiding path at a vertex

Both remaining pieces of Osin's §4 need the same operation: cut a path at a
vertex and treat the two halves separately.  The transport of local finiteness
cuts at the first new letter read inside `H`; the complementary-path argument for
an isolated component cuts at the component's two endpoints.  This module
supplies the cut, once.

* `vertex_eq_mul_listVal_take` --- **the `j`-th vertex is what the first `j`
  letters spell**, `vertex v w j = v · listVal (w.take j)`, with no hypothesis on
  `j`: past the end of the word both sides are `v · listVal w`.  This is the
  identification the whole §4 index bookkeeping rests on, and
  `GGT/OsinPenetration.lean` has it only at `j = w.length`.
* `avoidsFrom_take`, `avoidsFrom_drop` --- **avoidance restricts to both
  halves**, the second read from the cut vertex.  Immediate from
  `avoidsFrom_append` once the vertex is identified.
* `mem_relBall_vertex` --- **a vertex of an avoiding path that lands in `H_λ` is
  within `d̂_λ`-distance `j` of `1`**: the first `j` letters are themselves an
  avoiding path to it.
* `mem_relBall_vertex_inv_mul` --- and the rest of the path, translated back to
  `1`, puts `(vertex v w j)⁻¹ · listVal w` in the ball of radius
  `w.length − j`.  Translating is legal because the cut vertex lies in `H_λ`, so
  `avoidsFrom_smul_left` applies.

Together these say that an avoiding path through a vertex of `H_λ` is the
concatenation of two avoiding paths, whose radii add up to its length.  That is
the recursion the transport argument runs on, and the decomposition the
complementary-path argument reads backwards.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The vertex reached is what the prefix spells -/

/-- **`vertex v w j = v · listVal (w.take j)`**, for every `j`.

No bound on `j` is needed: past the end of the word the vertex map stalls at
`v · listVal w`, and so does the prefix. -/
theorem vertex_eq_mul_listVal_take :
    ∀ (w : List (RelLetter G Λ)) (v : G) (j : ℕ),
      vertex v w j = v * RelLetter.listVal (w.take j) := by
  intro w
  induction w with
  | nil =>
      intro v j
      rw [List.take_nil, RelLetter.listVal_nil, mul_one, vertex_nil]
  | cons a t ih =>
      intro v j
      cases j with
      | zero =>
          rw [vertex_zero, List.take_zero, RelLetter.listVal_nil, mul_one]
      | succ j' =>
          rw [vertex_cons_succ, ih (v * a.val) j', List.take_succ_cons,
            listVal_cons, mul_assoc]

/-! ## Avoidance restricts to both halves -/

/-- The first `j` letters of an avoiding path are an avoiding path. -/
theorem avoidsFrom_take (H : Λ → Subgroup G) (lam : Λ) (v : G)
    (w : List (RelLetter G Λ)) (j : ℕ) (hav : AvoidsFrom H lam w v) :
    AvoidsFrom H lam (w.take j) v := by
  have hsplit : w.take j ++ w.drop j = w := List.take_append_drop j w
  have happ := avoidsFrom_append H lam (w.take j) (w.drop j) v
  rw [hsplit] at happ
  exact (happ.mp hav).1

/-- The remaining letters are an avoiding path from the cut vertex. -/
theorem avoidsFrom_drop (H : Λ → Subgroup G) (lam : Λ) (v : G)
    (w : List (RelLetter G Λ)) (j : ℕ) (hav : AvoidsFrom H lam w v) :
    AvoidsFrom H lam (w.drop j) (vertex v w j) := by
  have hsplit : w.take j ++ w.drop j = w := List.take_append_drop j w
  have happ := avoidsFrom_append H lam (w.take j) (w.drop j) v
  rw [hsplit] at happ
  have h2 := (happ.mp hav).2
  rwa [← vertex_eq_mul_listVal_take w v j] at h2

/-! ## The two halves as relative balls -/

/-- **A vertex of an avoiding path that lies in `H lam` is `d̂_lam`-close to `1`**:
the prefix reaching it is itself an avoiding path, of length at most `j`. -/
theorem mem_relBall_vertex (D : RelGenSet G Λ) (lam : Λ)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a)
    (hav : AvoidsFrom D.fam lam w 1) (j : ℕ)
    (hmem : vertex (1 : G) w j ∈ D.fam lam) :
    vertex (1 : G) w j ∈ D.relBall lam j := by
  refine ⟨hmem, w.take j, ?_, ?_, avoidsFrom_take D.fam lam 1 w j hav, ?_⟩
  · intro a ha
    exact hlet a (List.take_subset j w ha)
  · rw [vertex_eq_mul_listVal_take w 1 j, one_mul]
  · rw [List.length_take]
    omega

/-- **And the rest of the path is an avoiding path back at `1`.**

The cut vertex lies in `H lam`, so translating the suffix by its inverse
preserves avoidance (`avoidsFrom_smul_left`); the translated path spells
`(vertex v w j)⁻¹ · listVal w` and has `w.length − j` letters. -/
theorem mem_relBall_vertex_inv_mul (D : RelGenSet G Λ) (lam : Λ)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a)
    (hav : AvoidsFrom D.fam lam w 1) (j : ℕ)
    (hmem : vertex (1 : G) w j ∈ D.fam lam)
    (hend : (vertex (1 : G) w j)⁻¹ * RelLetter.listVal w ∈ D.fam lam) :
    (vertex (1 : G) w j)⁻¹ * RelLetter.listVal w
      ∈ D.relBall lam (w.length - j) := by
  have hdrop := avoidsFrom_drop D.fam lam 1 w j hav
  have hinv : (vertex (1 : G) w j)⁻¹ ∈ D.fam lam := inv_mem hmem
  have htrans :
      AvoidsFrom D.fam lam (w.drop j) ((vertex (1 : G) w j)⁻¹ * vertex (1 : G) w j)
        ↔ AvoidsFrom D.fam lam (w.drop j) (vertex (1 : G) w j) :=
    avoidsFrom_smul_left hinv (w.drop j) (vertex (1 : G) w j)
  rw [inv_mul_cancel] at htrans
  have hval : RelLetter.listVal (w.drop j)
      = (vertex (1 : G) w j)⁻¹ * RelLetter.listVal w := by
    have hsplit : w.take j ++ w.drop j = w := List.take_append_drop j w
    have hprod : RelLetter.listVal (w.take j) * RelLetter.listVal (w.drop j)
        = RelLetter.listVal w := by
      rw [← listVal_append, hsplit]
    have hpre : RelLetter.listVal (w.take j) = vertex (1 : G) w j := by
      rw [vertex_eq_mul_listVal_take w 1 j, one_mul]
    rw [← hprod, hpre, inv_mul_cancel_left]
  refine ⟨hend, w.drop j, ?_, hval, htrans.mpr hdrop, ?_⟩
  · intro a ha
    exact hlet a (List.drop_subset j w ha)
  · rw [List.length_drop]

end OsinComponents
end GGT
end GroupApproximation
