import GroupApproximation.CharClass.SteenrodCochain

/-!
# The cup-`i` coboundary formula

```text
δ(α ⌣ᵢ₊₁ β) = δα ⌣ᵢ₊₁ β + α ⌣ᵢ₊₁ δβ + α ⌣ᵢ β + β ⌣ᵢ α        (mod 2)
```

with all five cochains at their literal degrees: the left side in degree `n+1`
and each right-hand term in degree `n+1` as well, so **no degree cast occurs**.
The identity holds for every quadruple `(i, a, b, n)`; when `a + b ≠ n + i + 1`
all five terms are the zero cochain (`cochainCupI_of_degree_ne`).

The whole content is the combinatorial `cut_coboundary_master` below, stated
for an arbitrary abelian group of exponent two, whose proof is:

* deleting a vertex of the ambient simplex commutes with cutting
  (`cutU_map_succAbove`), so the left side is a sum over cuts `T` of the big
  simplex and vertices `k ∉ T`;
* each such term matches one term of `δα ⌣ β` or of `α ⌣ δβ`, and the terms of
  those two sums that are left over are exactly the ones where the deleted
  vertex **is** a cut point;
* those leftovers telescope, by `cut_insert_cancel`, to `α ⌣ᵢ β + β ⌣ᵢ α`.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial SimplexCategory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation
namespace CharClass

/-! ## 1. Three bookkeeping lemmas -/

/-- In characteristic two an equation can be moved across a sum. -/
theorem char2_move {M : Type*} [AddCommGroup M] (h2 : ∀ x : M, x + x = 0) {A B C : M}
    (h : A = B + C) : B = A + C := by
  rw [h]
  have hrw : B + C + C = B + (C + C) := by abel
  rw [hrw, h2, add_zero]

theorem sum_compl_swap {M : Type*} [AddCommMonoid M] {N : ℕ} (s : Finset (Finset (Fin N)))
    (F : Fin N → Finset (Fin N) → M) :
    ∑ k : Fin N, ∑ T ∈ s.filter (fun T => k ∉ T), F k T = ∑ T ∈ s, ∑ k ∈ Tᶜ, F k T := by
  classical
  calc ∑ k : Fin N, ∑ T ∈ s.filter (fun T => k ∉ T), F k T
      = ∑ k : Fin N, ∑ T ∈ s, if k ∉ T then F k T else 0 :=
        Finset.sum_congr rfl fun k _ => Finset.sum_filter _ _
    _ = ∑ T ∈ s, ∑ k : Fin N, if k ∉ T then F k T else 0 := Finset.sum_comm
    _ = ∑ T ∈ s, ∑ k ∈ Tᶜ, F k T := by
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]

/-- A vertex outside the cut set is deleted from exactly one of the two
families, so the sum over the complement of the cut set splits. -/
theorem sum_erase_split {M : Type*} [AddCommMonoid M] {N : ℕ} (T : Finset (Fin N))
    (Θ : Finset (Fin N) → Finset (Fin N) → M) :
    ∑ k ∈ (Tᶜ : Finset (Fin N)), Θ ((cutU T).erase k) ((cutV T).erase k)
      = (∑ k ∈ cutU T \ T, Θ ((cutU T).erase k) (cutV T))
        + ∑ k ∈ cutV T \ T, Θ (cutU T) ((cutV T).erase k) := by
  classical
  have hunion : (Tᶜ : Finset (Fin N)) = (cutU T \ T) ∪ (cutV T \ T) := by
    ext k
    simp only [Finset.mem_compl, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro hk
      have hall : k ∈ cutU T ∪ cutV T := by
        rw [cutU_union_cutV]
        exact Finset.mem_univ k
      rcases Finset.mem_union.1 hall with h | h
      · exact Or.inl ⟨h, hk⟩
      · exact Or.inr ⟨h, hk⟩
    · rintro (⟨-, hk⟩ | ⟨-, hk⟩) <;> exact hk
  have hdisj : Disjoint (cutU T \ T) (cutV T \ T) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    obtain ⟨hkU, hkT⟩ := Finset.mem_sdiff.1 hk
    obtain ⟨hkV, -⟩ := Finset.mem_sdiff.1 hk'
    exact hkT (by rw [← cutU_inter_cutV T]; exact Finset.mem_inter.2 ⟨hkU, hkV⟩)
  rw [hunion, Finset.sum_union hdisj]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hkU, hkT⟩ := Finset.mem_sdiff.1 hk
    rw [Finset.erase_eq_of_notMem (not_mem_cutV_of_mem_cutU hkT hkU)]
  · refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hkV, hkT⟩ := Finset.mem_sdiff.1 hk
    have hkU : k ∉ cutU T := by
      intro hh
      exact hkT (by rw [← cutU_inter_cutV T]; exact Finset.mem_inter.2 ⟨hh, hkV⟩)
    rw [Finset.erase_eq_of_notMem hkU]

/-! ## 2. The master identity -/

/-- **The coboundary formula, as pure combinatorics.**  `Θ` assigns a value to
a pair of faces of a fixed `(n+1)`-simplex.  The left side is what the
coboundary of `⌣ᵢ₊₁` produces; the four sums on the right are what
`δα ⌣ᵢ₊₁ β`, `α ⌣ᵢ₊₁ δβ`, `α ⌣ᵢ β` and `β ⌣ᵢ α` produce. -/
theorem cut_coboundary_master {M : Type*} [AddCommGroup M] (h2 : ∀ x : M, x + x = 0)
    {n : ℕ} (m : ℕ) (Θ : Finset (Fin (n + 2)) → Finset (Fin (n + 2)) → M) :
    (∑ k : Fin (n + 2), ∑ S ∈ cutIndex (m + 1) n,
        Θ ((cutU (S.map (Fin.succAboveOrderEmb k).toEmbedding)).erase k)
          ((cutV (S.map (Fin.succAboveOrderEmb k).toEmbedding)).erase k))
      = (∑ T ∈ cutIndex (m + 1) (n + 1), ∑ c ∈ cutU T, Θ ((cutU T).erase c) (cutV T))
        + (∑ T ∈ cutIndex (m + 1) (n + 1), ∑ c ∈ cutV T, Θ (cutU T) ((cutV T).erase c))
        + (∑ T ∈ cutIndex m (n + 1), Θ (cutU T) (cutV T))
        + (∑ T ∈ cutIndex m (n + 1), Θ (cutV T) (cutU T)) := by
  classical
  have step1 : ∀ k : Fin (n + 2),
      (∑ S ∈ cutIndex (m + 1) n,
          Θ ((cutU (S.map (Fin.succAboveOrderEmb k).toEmbedding)).erase k)
            ((cutV (S.map (Fin.succAboveOrderEmb k).toEmbedding)).erase k))
        = ∑ T ∈ (cutIndex (m + 1) (n + 1)).filter (fun T => k ∉ T),
            Θ ((cutU T).erase k) ((cutV T).erase k) :=
    fun k => sum_cutIndex_map (m + 1) n k (fun T => Θ ((cutU T).erase k) ((cutV T).erase k))
  have estep1 :
      (∑ k : Fin (n + 2), ∑ S ∈ cutIndex (m + 1) n,
          Θ ((cutU (S.map (Fin.succAboveOrderEmb k).toEmbedding)).erase k)
            ((cutV (S.map (Fin.succAboveOrderEmb k).toEmbedding)).erase k))
        = ∑ k : Fin (n + 2), ∑ T ∈ (cutIndex (m + 1) (n + 1)).filter (fun T => k ∉ T),
            Θ ((cutU T).erase k) ((cutV T).erase k) :=
    Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => step1 k)
  have eswap :
      (∑ k : Fin (n + 2), ∑ T ∈ (cutIndex (m + 1) (n + 1)).filter (fun T => k ∉ T),
          Θ ((cutU T).erase k) ((cutV T).erase k))
        = ∑ T ∈ cutIndex (m + 1) (n + 1), ∑ k ∈ (Tᶜ : Finset (Fin (n + 2))),
            Θ ((cutU T).erase k) ((cutV T).erase k) :=
    sum_compl_swap (cutIndex (m + 1) (n + 1))
      (fun k T => Θ ((cutU T).erase k) ((cutV T).erase k))
  have step2 : ∀ T ∈ cutIndex (m + 1) (n + 1),
      (∑ k ∈ (Tᶜ : Finset (Fin (n + 2))), Θ ((cutU T).erase k) ((cutV T).erase k))
        = ((∑ c ∈ cutU T, Θ ((cutU T).erase c) (cutV T))
            + (∑ c ∈ cutV T, Θ (cutU T) ((cutV T).erase c)))
          + ((∑ c ∈ T, Θ ((cutU T).erase c) (cutV T))
            + (∑ c ∈ T, Θ (cutU T) ((cutV T).erase c))) := by
    intro T _
    rw [sum_erase_split T Θ, char2_move h2 (Finset.sum_sdiff (subset_cutU T)).symm,
      char2_move h2 (Finset.sum_sdiff (subset_cutV T)).symm]
    abel
  have hBD :
      (∑ T ∈ cutIndex (m + 1) (n + 1), ∑ c ∈ T, Θ ((cutU T).erase c) (cutV T))
        + (∑ T ∈ cutIndex (m + 1) (n + 1), ∑ c ∈ T, Θ (cutU T) ((cutV T).erase c))
      = (∑ T ∈ cutIndex m (n + 1), Θ (cutU T) (cutV T))
        + (∑ T ∈ cutIndex m (n + 1), Θ (cutV T) (cutU T)) := by
    have hmerge : ∀ T ∈ cutIndex (m + 1) (n + 1),
        ((∑ c ∈ T, Θ ((cutU T).erase c) (cutV T)) + ∑ c ∈ T, Θ (cutU T) ((cutV T).erase c))
          = ∑ c ∈ T,
              (Θ ((cutU (insert c (T.erase c))).erase c) (cutV (insert c (T.erase c)))
                + Θ (cutU (insert c (T.erase c))) ((cutV (insert c (T.erase c))).erase c)) := by
      intro T _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [Finset.insert_erase hc]
    have hreindex :
        (∑ T ∈ cutIndex (m + 1) (n + 1), ∑ c ∈ T,
            (Θ ((cutU (insert c (T.erase c))).erase c) (cutV (insert c (T.erase c)))
              + Θ (cutU (insert c (T.erase c))) ((cutV (insert c (T.erase c))).erase c)))
          = ∑ T ∈ cutIndex m (n + 1), ∑ c ∈ (Tᶜ : Finset (Fin (n + 2))),
              (Θ ((cutU (insert c T)).erase c) (cutV (insert c T))
                + Θ (cutU (insert c T)) ((cutV (insert c T)).erase c)) :=
      sum_cutIndex_succ_erase m (n + 1) (fun T c =>
        Θ ((cutU (insert c T)).erase c) (cutV (insert c T))
          + Θ (cutU (insert c T)) ((cutV (insert c T)).erase c))
    have hcancel :
        (∑ T ∈ cutIndex m (n + 1), ∑ c ∈ (Tᶜ : Finset (Fin (n + 2))),
            (Θ ((cutU (insert c T)).erase c) (cutV (insert c T))
              + Θ (cutU (insert c T)) ((cutV (insert c T)).erase c)))
          = ∑ T ∈ cutIndex m (n + 1), (Θ (cutU T) (cutV T) + Θ (cutV T) (cutU T)) :=
      Finset.sum_congr rfl (fun T (_ : T ∈ cutIndex m (n + 1)) => cut_insert_cancel h2 Θ T)
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hmerge, hreindex, hcancel,
      Finset.sum_add_distrib]
  rw [estep1, eswap, Finset.sum_congr rfl step2, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, hBD]
  abel

/-! ## 3. Two degenerate cuts -/

theorem cutRank_empty {N : ℕ} (x : Fin N) : cutRank (∅ : Finset (Fin N)) x = 0 := by
  unfold cutRank
  rw [Finset.filter_empty, Finset.card_empty]

theorem cutV_empty {N : ℕ} : cutV (∅ : Finset (Fin N)) = ∅ := by
  ext x
  rw [mem_cutV, cutRank_empty]
  simp

theorem cutIndex_zero (n : ℕ) : cutIndex 0 n = {(∅ : Finset (Fin (n + 1)))} := by
  ext S
  rw [mem_cutIndex, Finset.mem_singleton, Finset.card_eq_zero]

/-! ## 4. The coboundary formula on cochains -/

/-- **Steenrod's coboundary formula for `⌣ᵢ₊₁`, mod 2.**  Every term lives in
degree `n + 1`; nothing is transported along a degree equality. -/
theorem cochainCupI_coboundary {X : TopCat.{0}} (i a b n : ℕ)
    (α : singularCochainGroup (ZMod 2) X a) (β : singularCochainGroup (ZMod 2) X b) :
    cochainCoboundary (ZMod 2) X n (cochainCupI (i + 1) a b n α β)
      = cochainCupI (i + 1) (a + 1) b (n + 1) (cochainCoboundary (ZMod 2) X a α) β
        + cochainCupI (i + 1) a (b + 1) (n + 1) α (cochainCoboundary (ZMod 2) X b β)
        + cochainCupI i a b (n + 1) α β
        + cochainCupI i b a (n + 1) β α := by
  classical
  apply cochain_ext
  intro τ
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  have hlhs : cochainEval (n + 1)
      (cochainCoboundary (ZMod 2) X n (cochainCupI (i + 1) a b n α β)) τ
      = ∑ k : Fin (n + 2), ∑ S ∈ cutIndex (i + 1 + 1) n,
          faceVal a α τ ((cutU (S.map (Fin.succAboveOrderEmb k).toEmbedding)).erase k)
            * faceVal b β τ ((cutV (S.map (Fin.succAboveOrderEmb k).toEmbedding)).erase k) := by
    rw [cochainCoboundary_eval]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [neg_one_pow_zmod2, one_mul, cochainCupI_eval]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [faceVal_faceSimplex a n α k τ (cutU S), faceVal_faceSimplex b n β k τ (cutV S),
      cutU_map_succAbove k S, cutV_map_succAbove k S]
  have hT1 : cochainEval (n + 1)
      (cochainCupI (i + 1) (a + 1) b (n + 1) (cochainCoboundary (ZMod 2) X a α) β) τ
      = ∑ T ∈ cutIndex (i + 1 + 1) (n + 1), ∑ c ∈ cutU T,
          faceVal a α τ ((cutU T).erase c) * faceVal b β τ (cutV T) := by
    rw [cochainCupI_eval]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [faceVal_coboundary a n α τ (cutU T), Finset.sum_mul]
  have hT2 : cochainEval (n + 1)
      (cochainCupI (i + 1) a (b + 1) (n + 1) α (cochainCoboundary (ZMod 2) X b β)) τ
      = ∑ T ∈ cutIndex (i + 1 + 1) (n + 1), ∑ c ∈ cutV T,
          faceVal a α τ (cutU T) * faceVal b β τ ((cutV T).erase c) := by
    rw [cochainCupI_eval]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [faceVal_coboundary b n β τ (cutV T), Finset.mul_sum]
  have hT3 : cochainEval (n + 1) (cochainCupI i a b (n + 1) α β) τ
      = ∑ T ∈ cutIndex (i + 1) (n + 1), faceVal a α τ (cutU T) * faceVal b β τ (cutV T) :=
    cochainCupI_eval i a b (n + 1) α β τ
  have hT4 : cochainEval (n + 1) (cochainCupI i b a (n + 1) β α) τ
      = ∑ T ∈ cutIndex (i + 1) (n + 1), faceVal a α τ (cutV T) * faceVal b β τ (cutU T) := by
    rw [cochainCupI_eval]
    exact Finset.sum_congr rfl fun T _ => mul_comm _ _
  rw [cochainEval_add, cochainEval_add, cochainEval_add, hlhs, hT1, hT2, hT3, hT4]
  exact cut_coboundary_master h2 (i + 1) (fun A B => faceVal a α τ A * faceVal b β τ B)

/-- **The Leibniz rule, the `i = 0` end of the same formula.**  There are no
lower terms because a cut with no cut points has an empty right family, and a
cochain evaluates to `0` on the empty face. -/
theorem cochainCupI_coboundary_zero {X : TopCat.{0}} (a b n : ℕ)
    (α : singularCochainGroup (ZMod 2) X a) (β : singularCochainGroup (ZMod 2) X b) :
    cochainCoboundary (ZMod 2) X n (cochainCupI 0 a b n α β)
      = cochainCupI 0 (a + 1) b (n + 1) (cochainCoboundary (ZMod 2) X a α) β
        + cochainCupI 0 a (b + 1) (n + 1) α (cochainCoboundary (ZMod 2) X b β) := by
  classical
  apply cochain_ext
  intro τ
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  have hlhs : cochainEval (n + 1)
      (cochainCoboundary (ZMod 2) X n (cochainCupI 0 a b n α β)) τ
      = ∑ k : Fin (n + 2), ∑ S ∈ cutIndex (0 + 1) n,
          faceVal a α τ ((cutU (S.map (Fin.succAboveOrderEmb k).toEmbedding)).erase k)
            * faceVal b β τ ((cutV (S.map (Fin.succAboveOrderEmb k).toEmbedding)).erase k) := by
    rw [cochainCoboundary_eval]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [neg_one_pow_zmod2, one_mul, cochainCupI_eval]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [faceVal_faceSimplex a n α k τ (cutU S), faceVal_faceSimplex b n β k τ (cutV S),
      cutU_map_succAbove k S, cutV_map_succAbove k S]
  have hT1 : cochainEval (n + 1)
      (cochainCupI 0 (a + 1) b (n + 1) (cochainCoboundary (ZMod 2) X a α) β) τ
      = ∑ T ∈ cutIndex (0 + 1) (n + 1), ∑ c ∈ cutU T,
          faceVal a α τ ((cutU T).erase c) * faceVal b β τ (cutV T) := by
    rw [cochainCupI_eval]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [faceVal_coboundary a n α τ (cutU T), Finset.sum_mul]
  have hT2 : cochainEval (n + 1)
      (cochainCupI 0 a (b + 1) (n + 1) α (cochainCoboundary (ZMod 2) X b β)) τ
      = ∑ T ∈ cutIndex (0 + 1) (n + 1), ∑ c ∈ cutV T,
          faceVal a α τ (cutU T) * faceVal b β τ ((cutV T).erase c) := by
    rw [cochainCupI_eval]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [faceVal_coboundary b n β τ (cutV T), Finset.mul_sum]
  have hvanish1 :
      (∑ T ∈ cutIndex 0 (n + 1), faceVal a α τ (cutU T) * faceVal b β τ (cutV T)) = 0 := by
    rw [cutIndex_zero, Finset.sum_singleton, cutV_empty]
    refine mul_eq_zero_of_right _ (faceVal_of_card_ne β τ ?_)
    rw [Finset.card_empty]
    omega
  have hvanish2 :
      (∑ T ∈ cutIndex 0 (n + 1), faceVal a α τ (cutV T) * faceVal b β τ (cutU T)) = 0 := by
    rw [cutIndex_zero, Finset.sum_singleton, cutV_empty]
    refine mul_eq_zero_of_left (faceVal_of_card_ne α τ ?_) _
    rw [Finset.card_empty]
    omega
  rw [cochainEval_add, hlhs, hT1, hT2]
  have hmaster :
      (∑ k : Fin (n + 2), ∑ S ∈ cutIndex (0 + 1) n,
          faceVal a α τ ((cutU (S.map (Fin.succAboveOrderEmb k).toEmbedding)).erase k)
            * faceVal b β τ ((cutV (S.map (Fin.succAboveOrderEmb k).toEmbedding)).erase k))
        = (∑ T ∈ cutIndex (0 + 1) (n + 1), ∑ c ∈ cutU T,
            faceVal a α τ ((cutU T).erase c) * faceVal b β τ (cutV T))
          + (∑ T ∈ cutIndex (0 + 1) (n + 1), ∑ c ∈ cutV T,
            faceVal a α τ (cutU T) * faceVal b β τ ((cutV T).erase c))
          + (∑ T ∈ cutIndex 0 (n + 1), faceVal a α τ (cutU T) * faceVal b β τ (cutV T))
          + (∑ T ∈ cutIndex 0 (n + 1), faceVal a α τ (cutV T) * faceVal b β τ (cutU T)) :=
    cut_coboundary_master h2 0 (fun A B => faceVal a α τ A * faceVal b β τ B)
  rw [hvanish1, hvanish2, add_zero, add_zero] at hmaster
  exact hmaster

end CharClass
end GroupApproximation
