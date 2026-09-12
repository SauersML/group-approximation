import GroupApproximation.Algebra.BowditchCorner

/-!
# Geodesic triangles read cyclically, and their corners

A geodesic triangle is recorded cyclically: geodesic words `γ₁` from `V₁` to `V₂`,
`γ₂` from `V₂` to `V₃` and `γ₃` from `V₃` back to `V₁`.  At each vertex the two
sides leaving it are the next word, read forwards, and the previous word, read
backwards as `revList`.  This makes every statement invariant under rotating the
triangle, which is how Bowditch's Lemma 6.2.3 avoids repeating its argument three
times.

This module converts vertices of a reversed word back to the original word
(`mul_prod_take_revList`), shows that the reversed word is geodesic with the same
vertices, and restates Bowditch's corner lemma at a vertex of a cyclic triangle in
terms of the original words (`exists_cyclicCorner`).
-/

namespace GroupApproximation
namespace DiscreteStokes

open WordMetric

universe v

variable {Q : Type v} [Group Q]

/-! ## Reversed words -/

/-- **A vertex of the reversed word is a vertex of the original word**, at the
complementary index. -/
theorem mul_prod_take_revList (V : Q) (γ : List Q) (k : ℕ) :
    V * γ.prod * ((revList γ).take k).prod = V * (γ.take (γ.length - k)).prod := by
  have e : (revList γ).take k = revList (γ.drop (γ.length - k)) := by
    unfold revList
    rw [List.take_reverse, List.length_map, List.map_drop]
  rw [e, prod_revList, ← List.prod_take_mul_prod_drop γ (γ.length - k)]
  group

/-- The reversed word visits the same vertices. -/
theorem distToList_listPoints_revList (S : Set Q) (g V : Q) (γ : List Q) :
    distToList S g (listPoints (V * γ.prod) (revList γ)) = distToList S g (listPoints V γ) :=
  le_antisymm
    (distToList_le_of_subset S g (listPoints_ne_nil _ _)
      (fun p hp => (mem_listPoints_revList V γ p).mpr hp))
    (distToList_le_of_subset S g (listPoints_ne_nil _ _)
      (fun p hp => (mem_listPoints_revList V γ p).mp hp))

/-- A reversed geodesic word is geodesic. -/
theorem isGeodesicWord_revList {S : Set Q} (hS : IsSymmetricGeneratingSet S) {γ : List Q}
    (hγ : IsGeodesicWord S γ γ.prod) : IsGeodesicWord S (revList γ) (revList γ).prod := by
  refine ⟨⟨letters_revList hS hγ.isWord.letters, rfl⟩, ?_⟩
  rw [length_revList, prod_revList, wordNorm_inv hS]
  exact hγ.length_eq

/-! ## A corner of a cyclic triangle -/

/-- **Bowditch's Lemma 6.2.2 at a vertex of a cyclic triangle**, in terms of the
original words.  The vertex is `V`, the side leaving it forwards is `γ` (to `W`), and
the side arriving at it is `δ` from `U` (so `U * δ.prod = V`).  If `W` is at distance at
least `R = 4 r + L` from `δ` and `U` at distance at least `R` from `γ`, there are
indices `i ≤ |γ|` and `k ≤ |δ|` with, writing `A = V γ[..i]` and
`B = U δ[..|δ| - k]`:

* `A` is at distance exactly `r` from `δ`, and every later vertex of `γ` at least `r`;
* every vertex of `δ` up to `B` is at distance at least `r` from `γ`;
* every vertex of `γ` up to `A` is within `r + L` of `δ`;
* `r ≤ d(A, B) ≤ R`. -/
theorem exists_cyclicCorner {S : Set Q} (hS : IsSymmetricGeneratingSet S) {r L : ℕ}
    (hr : 0 < r) (hH4 : BowditchH4 S r L) {U V : Q} {γ δ : List Q}
    (hγ : IsGeodesicWord S γ γ.prod) (hδ : IsGeodesicWord S δ δ.prod) (hUV : U * δ.prod = V)
    (hW : 4 * r + L ≤ distToList S (V * γ.prod) (listPoints U δ))
    (hU : 4 * r + L ≤ distToList S U (listPoints V γ)) :
    ∃ i k : ℕ, i ≤ γ.length ∧ k ≤ δ.length ∧
      distToList S (V * (γ.take i).prod) (listPoints U δ) = r ∧
      (∀ t, i ≤ t → r ≤ distToList S (V * (γ.take t).prod) (listPoints U δ)) ∧
      (∀ s, s ≤ δ.length - k → r ≤ distToList S (U * (δ.take s).prod) (listPoints V γ)) ∧
      (∀ t, t ≤ i → distToList S (V * (γ.take t).prod) (listPoints U δ) ≤ r + L) ∧
      r ≤ wordDist S (V * (γ.take i).prod) (U * (δ.take (δ.length - k)).prod) ∧
      wordDist S (V * (γ.take i).prod) (U * (δ.take (δ.length - k)).prod) ≤ 4 * r + L := by
  have hrev := isGeodesicWord_revList hS hδ
  have hVprod : V * (revList δ).prod = U := by
    rw [prod_revList, ← hUV]
    group
  have hPts : ∀ g, distToList S g (listPoints V (revList δ)) =
      distToList S g (listPoints U δ) := by
    intro g
    rw [← hUV]
    exact distToList_listPoints_revList S g U δ
  obtain ⟨i, k, hi, hk, hAeq, hfar₁, hfar₂, _hnear₂, hnear₁, hlow, hup⟩ :=
    exists_corner_of_bowditchH4 hS hr hH4 (X := V) hγ hrev
      (by rw [hPts]; exact hW) (by rw [hVprod]; exact hU)
  rw [length_revList] at hk
  have hB : V * ((revList δ).take k).prod = U * (δ.take (δ.length - k)).prod := by
    rw [← hUV]
    exact mul_prod_take_revList U δ k
  refine ⟨i, k, hi, hk, by rw [← hPts]; exact hAeq,
    fun t ht => by rw [← hPts]; exact hfar₁ t ht, ?_, ?_,
    by rw [← hB]; exact hlow, by rw [← hB]; exact hup⟩
  · intro s hs
    have h := hfar₂ (δ.length - s) (by omega) (by rw [length_revList]; omega)
    rw [← hUV, mul_prod_take_revList U δ (δ.length - s),
      Nat.sub_sub_self (show s ≤ δ.length by omega)] at h
    rw [← hUV]
    exact h
  · intro t ht
    have h := hnear₁ t ht
    have hsub : distToList S (V * (γ.take t).prod) (listPoints V (revList δ)) ≤
        distToList S (V * (γ.take t).prod) (listPoints V ((revList δ).take k)) := by
      refine distToList_le_of_subset S _ (listPoints_ne_nil _ _) ?_
      intro p hp
      obtain ⟨m, rfl⟩ := (mem_listPoints_iff _ _ _).mp hp
      rw [List.take_take]
      exact take_mem_listPoints V (revList δ) _
    rw [← hPts]
    omega

end DiscreteStokes
end GroupApproximation

#audit_axioms GroupApproximation.DiscreteStokes.mul_prod_take_revList
#audit_axioms GroupApproximation.DiscreteStokes.distToList_listPoints_revList
#audit_axioms GroupApproximation.DiscreteStokes.isGeodesicWord_revList
#audit_axioms GroupApproximation.DiscreteStokes.exists_cyclicCorner
