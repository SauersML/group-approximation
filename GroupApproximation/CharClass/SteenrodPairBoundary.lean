import GroupApproximation.CharClass.SteenrodDiagonal
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The two halves of the boundary on `S(X) ⊗ S(X)`, against the cut diagonal

The chain-map condition for Steenrod's diagonal compares the differential of the
target with the differential of the source.  The target's differential is
`∂ ⊗ 1 + 1 ⊗ ∂`, and this file is the bidegreewise reading of its two halves:
`tenBdL` and `tenBdR`, acting on `tensorTwo X a b`.

Two things are proved about them.

* `tenBdL_facePair` / `tenBdR_facePair` — the boundary of a *face pair* is the
  sum over the vertices of the corresponding family of the face pairs obtained by
  deleting one.  These are the `facePair`-valued analogues of
  `SteenrodCochain.faceVal_coboundary`, with the same proof: the `j`-th face of
  the face spanned by `A` is the face spanned by `A` with its `j`-th element
  removed, and `Finset.orderEmbOfFin` is the bijection `Fin (a+2) ≃ A`.

* `steenrodDiag_boundary'` and `steenrodDiag_boundary_zero'` — the boundary
  identity of `SteenrodDiagonal.lean`, restated with its two middle sums
  recognised as `tenBdL` and `tenBdR`.  In that form it says exactly

  ```text
  Φ(e_i ⊗ ∂σ) = ∂ Φ(e_i ⊗ σ) + Φ(e_{i-1} ⊗ σ) + T Φ(e_{i-1} ⊗ σ)
  ```

  with the last two terms present precisely when `i ≥ 1`.  The `i = 0` case is
  the same master identity at `m = 0`: the low terms then run over
  `cutIndex 0 (n+1) = {∅}`, and `cutV ∅ = ∅` has no vertices, so both vanish.
  That is the Alexander–Whitney end, where `Φ` is an honest chain map on the
  nose.

Nothing here mentions the group ring or the swap action; those enter in
`SteenrodPairCell.lean`.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial SimplexCategory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

variable {X : TopCat.{0}}

/-! ## 1. Recognising and killing a face pair -/

theorem facePair_of_card (a b : ℕ) {n : ℕ} (σ : singularSimplices X n)
    {A B : Finset (Fin (n + 1))} (hA : A.card = a + 1) (hB : B.card = b + 1) :
    facePair a b σ A B
      = Finsupp.single
          (restrictSimplex (faceOfFinset A hA) σ, restrictSimplex (faceOfFinset B hB) σ) 1 := by
  unfold facePair
  rw [dif_pos hA, dif_pos hB]

theorem facePair_eq_zero_left (a b : ℕ) {n : ℕ} (σ : singularSimplices X n)
    {A B : Finset (Fin (n + 1))} (hA : ¬ A.card = a + 1) : facePair a b σ A B = 0 := by
  unfold facePair
  rw [dif_neg hA]

theorem facePair_eq_zero_right (a b : ℕ) {n : ℕ} (σ : singularSimplices X n)
    {A B : Finset (Fin (n + 1))} (hB : ¬ B.card = b + 1) : facePair a b σ A B = 0 := by
  unfold facePair
  by_cases hA : A.card = a + 1
  · rw [dif_pos hA, dif_neg hB]
  · rw [dif_neg hA]

/-! ## 2. The two halves of the boundary in one bidegree -/

/-- `∂ ⊗ 1` in bidegree `(a+1, b)`: the boundary of the left factor. -/
def tenBdL (X : TopCat.{0}) (a b : ℕ) : tensorTwo X (a + 1) b →ₗ[ZMod 2] tensorTwo X a b :=
  Finsupp.linearCombination (ZMod 2)
    (fun p : singularSimplices X (a + 1) × singularSimplices X b =>
      ∑ j : Fin (a + 2), Finsupp.single (faceSimplex X a j p.1, p.2) (1 : ZMod 2))

/-- `1 ⊗ ∂` in bidegree `(a, b+1)`: the boundary of the right factor. -/
def tenBdR (X : TopCat.{0}) (a b : ℕ) : tensorTwo X a (b + 1) →ₗ[ZMod 2] tensorTwo X a b :=
  Finsupp.linearCombination (ZMod 2)
    (fun p : singularSimplices X a × singularSimplices X (b + 1) =>
      ∑ j : Fin (b + 2), Finsupp.single (p.1, faceSimplex X b j p.2) (1 : ZMod 2))

theorem tenBdL_single (a b : ℕ) (p : singularSimplices X (a + 1) × singularSimplices X b) :
    tenBdL X a b (Finsupp.single p 1)
      = ∑ j : Fin (a + 2), Finsupp.single (faceSimplex X a j p.1, p.2) (1 : ZMod 2) := by
  unfold tenBdL
  simp

theorem tenBdR_single (a b : ℕ) (p : singularSimplices X a × singularSimplices X (b + 1)) :
    tenBdR X a b (Finsupp.single p 1)
      = ∑ j : Fin (b + 2), Finsupp.single (p.1, faceSimplex X b j p.2) (1 : ZMod 2) := by
  unfold tenBdR
  simp

/-! ## 3. The boundary of a face pair -/

/-- **`∂ ⊗ 1` on a face pair.**  Deleting a vertex of the left family, summed
over the vertices.  Both sides vanish when either family has the wrong size. -/
theorem tenBdL_facePair (a b : ℕ) {n : ℕ} (σ : singularSimplices X n)
    (A B : Finset (Fin (n + 1))) :
    tenBdL X a b (facePair (a + 1) b σ A B) = ∑ c ∈ A, facePair a b σ (A.erase c) B := by
  classical
  by_cases hB : B.card = b + 1
  · by_cases hA : A.card = a + 1 + 1
    · rw [facePair_of_card (a + 1) b σ hA hB, tenBdL_single]
      have hterm : ∀ j : Fin (a + 2),
          Finsupp.single
              (faceSimplex X a j (restrictSimplex (faceOfFinset A hA) σ),
                restrictSimplex (faceOfFinset B hB) σ) (1 : ZMod 2)
            = facePair a b σ (A.erase (A.orderEmbOfFin hA j)) B := by
        intro j
        have hcard : (A.erase (A.orderEmbOfFin hA j)).card = a + 1 := by
          have := Finset.card_erase_of_mem (A.orderEmbOfFin_mem hA j)
          omega
        rw [facePair_of_card a b σ hcard hB]
        refine congrArg
          (fun ρ => Finsupp.single (ρ, restrictSimplex (faceOfFinset B hB) σ) (1 : ZMod 2)) ?_
        rw [faceSimplex_eq_restrictSimplex, restrictSimplex_comp, delta_comp_faceOfFinset]
      rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hterm j)]
      refine Finset.sum_bij (fun (j : Fin (a + 2)) _ => A.orderEmbOfFin hA j) ?_ ?_ ?_ ?_
      · intro j _
        exact A.orderEmbOfFin_mem hA j
      · intro j₁ _ j₂ _ heq
        exact (A.orderEmbOfFin hA).injective heq
      · intro c hc
        have hrange : c ∈ Set.range (A.orderEmbOfFin hA) := by
          rw [Finset.range_orderEmbOfFin]
          exact Finset.mem_coe.2 hc
        obtain ⟨j, hj⟩ := hrange
        exact ⟨j, Finset.mem_univ j, hj⟩
      · intro j _
        rfl
    · rw [facePair_eq_zero_left (a + 1) b σ hA, map_zero]
      refine (Finset.sum_eq_zero ?_).symm
      intro c hc
      refine facePair_eq_zero_left a b σ ?_
      have hce := Finset.card_erase_of_mem hc
      have hpos : 1 ≤ A.card := Finset.card_pos.2 ⟨c, hc⟩
      omega
  · rw [facePair_eq_zero_right (a + 1) b σ hB, map_zero]
    refine (Finset.sum_eq_zero ?_).symm
    intro c _
    exact facePair_eq_zero_right a b σ hB

/-- **`1 ⊗ ∂` on a face pair.**  The mirror of `tenBdL_facePair`. -/
theorem tenBdR_facePair (a b : ℕ) {n : ℕ} (σ : singularSimplices X n)
    (A B : Finset (Fin (n + 1))) :
    tenBdR X a b (facePair a (b + 1) σ A B) = ∑ c ∈ B, facePair a b σ A (B.erase c) := by
  classical
  by_cases hA : A.card = a + 1
  · by_cases hB : B.card = b + 1 + 1
    · rw [facePair_of_card a (b + 1) σ hA hB, tenBdR_single]
      have hterm : ∀ j : Fin (b + 2),
          Finsupp.single
              (restrictSimplex (faceOfFinset A hA) σ,
                faceSimplex X b j (restrictSimplex (faceOfFinset B hB) σ)) (1 : ZMod 2)
            = facePair a b σ A (B.erase (B.orderEmbOfFin hB j)) := by
        intro j
        have hcard : (B.erase (B.orderEmbOfFin hB j)).card = b + 1 := by
          have := Finset.card_erase_of_mem (B.orderEmbOfFin_mem hB j)
          omega
        rw [facePair_of_card a b σ hA hcard]
        refine congrArg
          (fun ρ => Finsupp.single (restrictSimplex (faceOfFinset A hA) σ, ρ) (1 : ZMod 2)) ?_
        rw [faceSimplex_eq_restrictSimplex, restrictSimplex_comp, delta_comp_faceOfFinset]
      rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hterm j)]
      refine Finset.sum_bij (fun (j : Fin (b + 2)) _ => B.orderEmbOfFin hB j) ?_ ?_ ?_ ?_
      · intro j _
        exact B.orderEmbOfFin_mem hB j
      · intro j₁ _ j₂ _ heq
        exact (B.orderEmbOfFin hB).injective heq
      · intro c hc
        have hrange : c ∈ Set.range (B.orderEmbOfFin hB) := by
          rw [Finset.range_orderEmbOfFin]
          exact Finset.mem_coe.2 hc
        obtain ⟨j, hj⟩ := hrange
        exact ⟨j, Finset.mem_univ j, hj⟩
      · intro j _
        rfl
    · rw [facePair_eq_zero_right a (b + 1) σ hB, map_zero]
      refine (Finset.sum_eq_zero ?_).symm
      intro c hc
      refine facePair_eq_zero_right a b σ ?_
      have hce := Finset.card_erase_of_mem hc
      have hpos : 1 ≤ B.card := Finset.card_pos.2 ⟨c, hc⟩
      omega
  · rw [facePair_eq_zero_left a (b + 1) σ hA, map_zero]
    refine (Finset.sum_eq_zero ?_).symm
    intro c _
    exact facePair_eq_zero_left a b σ hA

/-! ## 4. The boundary of the cut diagonal -/

theorem tenBdL_steenrodDiag (i a b : ℕ) {N : ℕ} (σ : singularSimplices X N) :
    tenBdL X a b (steenrodDiag i (a + 1) b σ)
      = ∑ T ∈ cutIndex (i + 1) N, ∑ c ∈ cutU T, facePair a b σ ((cutU T).erase c) (cutV T) := by
  unfold steenrodDiag
  rw [map_sum]
  exact Finset.sum_congr rfl fun T _ => tenBdL_facePair a b σ (cutU T) (cutV T)

theorem tenBdR_steenrodDiag (i a b : ℕ) {N : ℕ} (σ : singularSimplices X N) :
    tenBdR X a b (steenrodDiag i a (b + 1) σ)
      = ∑ T ∈ cutIndex (i + 1) N, ∑ c ∈ cutV T, facePair a b σ (cutU T) ((cutV T).erase c) := by
  unfold steenrodDiag
  rw [map_sum]
  exact Finset.sum_congr rfl fun T _ => tenBdR_facePair a b σ (cutU T) (cutV T)

/-- The cut diagonal vanishes above the dimension of the simplex: there are no
`(i+1)`-element sets of cut points in an `N`-simplex once `i > N`. -/
theorem steenrodDiag_eq_zero_of_lt (i a b : ℕ) {N : ℕ} (σ : singularSimplices X N)
    (h : N < i) : steenrodDiag i a b σ = 0 := by
  unfold steenrodDiag
  have hempty : cutIndex (i + 1) N = ∅ := by
    unfold cutIndex
    rw [Finset.powersetCard_eq_empty, Finset.card_univ, Fintype.card_fin]
    omega
  rw [hempty, Finset.sum_empty]

/-! ## 5. The boundary identity, with the two middle sums recognised -/

/-- The sum of the cut diagonals over the faces of `σ`, written on the cut sets
of `σ` itself.  This is the left-hand side of the master identity, for every cut
size at once. -/
theorem steenrodDiag_face_sum (m a b n : ℕ) (σ : singularSimplices X (n + 1)) :
    (∑ k : Fin (n + 2), steenrodDiag m a b (faceSimplex X n k σ))
      = ∑ k : Fin (n + 2), ∑ S ∈ cutIndex (m + 1) n,
          facePair a b σ ((cutU (S.map (Fin.succAboveOrderEmb k).toEmbedding)).erase k)
            ((cutV (S.map (Fin.succAboveOrderEmb k).toEmbedding)).erase k) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold steenrodDiag
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [facePair_faceSimplex a b n k σ (cutU S) (cutV S), cutU_map_succAbove k S,
    cutV_map_succAbove k S]

/-- **The boundary identity, in operator form.**  `Φ(e_{i+1} ⊗ ∂σ)` is the
boundary of `Φ(e_{i+1} ⊗ σ)` plus `(1 + T) Φ(e_i ⊗ σ)`. -/
theorem steenrodDiag_boundary' (i a b n : ℕ) (σ : singularSimplices X (n + 1)) :
    (∑ jj : Fin (n + 2), steenrodDiag (i + 1) a b (faceSimplex X n jj σ))
      = tenBdL X a b (steenrodDiag (i + 1) (a + 1) b σ)
        + tenBdR X a b (steenrodDiag (i + 1) a (b + 1) σ)
        + steenrodDiag i a b σ
        + tensorSwap b a (steenrodDiag i b a σ) := by
  rw [tenBdL_steenrodDiag, tenBdR_steenrodDiag]
  exact steenrodDiag_boundary i a b n σ

/-- **The Alexander–Whitney end of the boundary identity.**  At `i = 0` the two
low terms of the master identity run over `cutIndex 0 (n+1) = {∅}`, and
`cutV ∅ = ∅` has no vertices, so both vanish: the diagonal is a chain map on the
nose. -/
theorem steenrodDiag_boundary_zero' (a b n : ℕ) (σ : singularSimplices X (n + 1)) :
    (∑ jj : Fin (n + 2), steenrodDiag 0 a b (faceSimplex X n jj σ))
      = tenBdL X a b (steenrodDiag 0 (a + 1) b σ)
        + tenBdR X a b (steenrodDiag 0 a (b + 1) σ) := by
  have hmaster := cut_coboundary_master (M := tensorTwo X a b) tensorTwo_add_self 0
    (fun A B => facePair a b σ A B)
  have hlow1 : (∑ T ∈ cutIndex 0 (n + 1), facePair a b σ (cutU T) (cutV T)) = 0 := by
    rw [cutIndex_zero (n + 1), Finset.sum_singleton, cutV_empty]
    refine facePair_eq_zero_right a b σ ?_
    rw [Finset.card_empty]
    omega
  have hlow2 : (∑ T ∈ cutIndex 0 (n + 1), facePair a b σ (cutV T) (cutU T)) = 0 := by
    rw [cutIndex_zero (n + 1), Finset.sum_singleton, cutV_empty]
    refine facePair_eq_zero_left a b σ ?_
    rw [Finset.card_empty]
    omega
  rw [steenrodDiag_face_sum 0 a b n σ, tenBdL_steenrodDiag, tenBdR_steenrodDiag, hmaster,
    hlow1, hlow2, add_zero, add_zero]

end

end Steenrod
end CharClass
end GroupApproximation
