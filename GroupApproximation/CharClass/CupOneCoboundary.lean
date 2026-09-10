import GroupApproximation.CharClass.CupOneCochain
import GroupApproximation.CharClass.CupOneInsert
import GroupApproximation.CharClass.SteenrodCoboundary

/-!
# Steenrod's cup-1 coboundary formula over an arbitrary commutative ring

```text
δ(α ⌣₁ β) = δα ⌣₁ β + (-1)^a (α ⌣₁ δβ) + (-1)^n (α ⌣ β) + (-1)^(a+b+ab) (β ⌣ α)
```

for `α` of degree `a`, `β` of degree `b`, the left cup-1 at literal output degree `n`
and every right-hand term at literal degree `n + 1`.  **No degree cast occurs**: as in
`SteenrodCoboundary.lean`, the output degree of the cup-1 is a free parameter and every
term of the wrong bidegree is the zero cochain.

For cocycles the two derivative terms vanish, and since `n = a + b - 1` wherever
anything is nonzero, the identity says

```text
α ⌣ β - (-1)^(a*b) (β ⌣ α) = (-1)^(a+b+1) δ(α ⌣₁ β),
```

which is graded commutativity on cohomology (`CupOneComm.lean`).

## The proof, and where it differs from the mod-2 one

The shape is `SteenrodCoboundary.cut_coboundary_master`, with two changes.

* The `(-1)^k` of the ambient coboundary and the cut's own sign are combined into
  `cupOneWeight T k`, and `cupOneSign_succAbove` — the two termwise identities of
  `CupOneSign.lean` — says the combination is a function of the **big** cut, which is
  what makes `sum_cutIndex_map` applicable.  This is why the sign is written through
  the face cardinalities: the identity then needs no degree hypothesis.
* The leftover, where the deleted vertex is itself a cut point, telescopes with a sign
  (`CupOneInsert.cut_insert_cancel_signed`) instead of cancelling in pairs.

Exactly two degree hypotheses survive, both discharged by a `by_cases` on a
cardinality inside a `Finset.sum_congr`: the coefficient `(-1)^a` of the second term is
`(-1)^((cutU T).card - 1)`, and the coefficient of `β ⌣ α` is `(-1)^(a+b+ab)`, only on
the cuts where the corresponding `faceVal` is nonzero.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial SimplexCategory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation
namespace CharClass

noncomputable section

/-! ## 1. The combined weight of a deleted vertex -/

/-- **The weight of the vertex `k` in the cut `T`**: the sign the coboundary formula
attaches to the term in which `k` is deleted from whichever of the two families of `T`
contains it. -/
def cupOneWeight (K : Type) [CommRing K] {N : ℕ} (T : Finset (Fin N)) (k : Fin N) : K :=
  if k ∈ cutU T then (-1 : K) ^ (cutExp T + cutRank (cutU T) k)
  else (-1 : K) ^ ((cutU T).card - 1 + cutExp T + cutRank (cutV T) k)

/-- **The termwise sign identity, in the ring.**  This is the whole sign bookkeeping of
the coboundary formula, and it holds for every two-point cut of the face and every
vertex of the simplex, with no degree hypothesis. -/
theorem cupOneSign_succAbove {K : Type} [CommRing K] {n : ℕ} (k : Fin (n + 2))
    (S : Finset (Fin (n + 1))) (hS : S.card = 2) :
    (-1 : K) ^ (k : ℕ) * cupOneSign K S
      = cupOneWeight K (S.map (Fin.succAboveOrderEmb k).toEmbedding) k := by
  obtain ⟨c₀, c₁, hlt, rfl⟩ := exists_pair_of_card_two hS
  rw [map_pair, cupOneSign_def, ← pow_add]
  unfold cupOneWeight
  by_cases hk : k ∈ cutU ({k.succAbove c₀, k.succAbove c₁} : Finset (Fin (n + 2)))
  · rw [if_pos hk]
    exact neg_one_pow_congr_mod_two (K := K)
      (cutExp_succAbove_cutU k hlt ((mem_cutU_map_pair k hlt).1 hk))
  · rw [if_neg hk]
    have hk' : ¬ (k.val ≤ c₀.val ∨ c₁.val < k.val) := fun hh =>
      hk ((mem_cutU_map_pair k hlt).2 hh)
    exact neg_one_pow_congr_mod_two (K := K)
      (cutExp_succAbove_cutV k hlt (by omega) (by omega))

/-! ## 2. Splitting the complement of a cut -/

/-- A vertex outside the cut lies in exactly one of the two families. -/
theorem sum_compl_split {M : Type*} [AddCommMonoid M] {N : ℕ} (T : Finset (Fin N))
    (G : Fin N → M) :
    ∑ k ∈ (Tᶜ : Finset (Fin N)), G k
      = (∑ k ∈ cutU T \ T, G k) + ∑ k ∈ cutV T \ T, G k := by
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

/-! ## 3. The signed master identity -/

/-- **The signed master identity.**  The generic replacement for
`SteenrodCoboundary.cut_coboundary_master`, specialised to two-point cuts (which is all
the cup-1 product uses) and stated directly on face evaluations so that no
higher-order rewriting is needed. -/
theorem cut_coboundary_master_signed {K : Type} [CommRing K] {X : TopCat.{0}} {n : ℕ}
    (a b : ℕ) (α : singularCochainGroup K X a) (β : singularCochainGroup K X b)
    (τ : singularSimplices X (n + 1)) :
    (∑ k : Fin (n + 2), ∑ S ∈ cutIndex 2 n,
        (-1 : K) ^ (k : ℕ) * (cupOneSign K S *
          (faceVal a α τ ((cutU (S.map (Fin.succAboveOrderEmb k).toEmbedding)).erase k)
            * faceVal b β τ ((cutV (S.map (Fin.succAboveOrderEmb k).toEmbedding)).erase k))))
      = (∑ T ∈ cutIndex 2 (n + 1), ∑ c ∈ cutU T,
            (-1 : K) ^ (cutExp T + cutRank (cutU T) c)
              * (faceVal a α τ ((cutU T).erase c) * faceVal b β τ (cutV T)))
        + (∑ T ∈ cutIndex 2 (n + 1), ∑ c ∈ cutV T,
            (-1 : K) ^ ((cutU T).card - 1 + cutExp T + cutRank (cutV T) c)
              * (faceVal a α τ (cutU T) * faceVal b β τ ((cutV T).erase c)))
        - ∑ S ∈ cutIndex 1 (n + 1),
            ((-1 : K) ^ (n + 2 + 1) * (faceVal a α τ (cutU S) * faceVal b β τ (cutV S))
              - (-1 : K) ^ (n + 2 + (n + 2) * ((cutU S).card - 1) + 1)
                  * (faceVal a α τ (cutV S) * faceVal b β τ (cutU S))) := by
  classical
  -- Step 1: the two signs combine into a function of the big cut, and the sum reindexes.
  have step1 : ∀ k : Fin (n + 2),
      (∑ S ∈ cutIndex 2 n, (-1 : K) ^ (k : ℕ) * (cupOneSign K S *
          (faceVal a α τ ((cutU (S.map (Fin.succAboveOrderEmb k).toEmbedding)).erase k)
            * faceVal b β τ ((cutV (S.map (Fin.succAboveOrderEmb k).toEmbedding)).erase k))))
        = ∑ T ∈ (cutIndex 2 (n + 1)).filter (fun T => k ∉ T),
            cupOneWeight K T k
              * (faceVal a α τ ((cutU T).erase k) * faceVal b β τ ((cutV T).erase k)) := by
    intro k
    rw [← sum_cutIndex_map 2 n k (fun T => cupOneWeight K T k
      * (faceVal a α τ ((cutU T).erase k) * faceVal b β τ ((cutV T).erase k)))]
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [← cupOneSign_succAbove k S (card_of_mem_cutIndex hS)]
    ring
  -- Step 2: swap the two sums.
  rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => step1 k),
    sum_compl_swap (cutIndex 2 (n + 1)) (fun k T => cupOneWeight K T k
      * (faceVal a α τ ((cutU T).erase k) * faceVal b β τ ((cutV T).erase k)))]
  -- Step 3: split each inner sum into the two families, and extract the cut points.
  have step3 : ∀ T ∈ cutIndex 2 (n + 1),
      (∑ k ∈ (Tᶜ : Finset (Fin (n + 2))), cupOneWeight K T k
          * (faceVal a α τ ((cutU T).erase k) * faceVal b β τ ((cutV T).erase k)))
        = (∑ c ∈ cutU T, (-1 : K) ^ (cutExp T + cutRank (cutU T) c)
              * (faceVal a α τ ((cutU T).erase c) * faceVal b β τ (cutV T)))
          + (∑ c ∈ cutV T, (-1 : K) ^ ((cutU T).card - 1 + cutExp T + cutRank (cutV T) c)
              * (faceVal a α τ (cutU T) * faceVal b β τ ((cutV T).erase c)))
          - ((∑ c ∈ T, (-1 : K) ^ (cutExp T + cutRank (cutU T) c)
                * (faceVal a α τ ((cutU T).erase c) * faceVal b β τ (cutV T)))
            + ∑ c ∈ T, (-1 : K) ^ ((cutU T).card - 1 + cutExp T + cutRank (cutV T) c)
                * (faceVal a α τ (cutU T) * faceVal b β τ ((cutV T).erase c))) := by
    intro T _
    rw [sum_compl_split T (fun k => cupOneWeight K T k
      * (faceVal a α τ ((cutU T).erase k) * faceVal b β τ ((cutV T).erase k)))]
    have hU : ∀ c ∈ cutU T \ T,
        cupOneWeight K T c
            * (faceVal a α τ ((cutU T).erase c) * faceVal b β τ ((cutV T).erase c))
          = (-1 : K) ^ (cutExp T + cutRank (cutU T) c)
              * (faceVal a α τ ((cutU T).erase c) * faceVal b β τ (cutV T)) := by
      intro c hc
      obtain ⟨hcU, hcT⟩ := Finset.mem_sdiff.1 hc
      rw [Finset.erase_eq_of_notMem (not_mem_cutV_of_mem_cutU hcT hcU)]
      unfold cupOneWeight
      rw [if_pos hcU]
    have hV : ∀ c ∈ cutV T \ T,
        cupOneWeight K T c
            * (faceVal a α τ ((cutU T).erase c) * faceVal b β τ ((cutV T).erase c))
          = (-1 : K) ^ ((cutU T).card - 1 + cutExp T + cutRank (cutV T) c)
              * (faceVal a α τ (cutU T) * faceVal b β τ ((cutV T).erase c)) := by
      intro c hc
      obtain ⟨hcV, hcT⟩ := Finset.mem_sdiff.1 hc
      have hcU : c ∉ cutU T := by
        intro hh
        exact hcT (by rw [← cutU_inter_cutV T]; exact Finset.mem_inter.2 ⟨hh, hcV⟩)
      rw [Finset.erase_eq_of_notMem hcU]
      unfold cupOneWeight
      rw [if_neg hcU]
    rw [Finset.sum_congr rfl hU, Finset.sum_congr rfl hV]
    have hsU : (∑ c ∈ cutU T \ T, (-1 : K) ^ (cutExp T + cutRank (cutU T) c)
            * (faceVal a α τ ((cutU T).erase c) * faceVal b β τ (cutV T)))
          + ∑ c ∈ T, (-1 : K) ^ (cutExp T + cutRank (cutU T) c)
              * (faceVal a α τ ((cutU T).erase c) * faceVal b β τ (cutV T))
        = ∑ c ∈ cutU T, (-1 : K) ^ (cutExp T + cutRank (cutU T) c)
            * (faceVal a α τ ((cutU T).erase c) * faceVal b β τ (cutV T)) :=
      Finset.sum_sdiff (subset_cutU T)
    have hsV : (∑ c ∈ cutV T \ T,
            (-1 : K) ^ ((cutU T).card - 1 + cutExp T + cutRank (cutV T) c)
              * (faceVal a α τ (cutU T) * faceVal b β τ ((cutV T).erase c)))
          + ∑ c ∈ T, (-1 : K) ^ ((cutU T).card - 1 + cutExp T + cutRank (cutV T) c)
              * (faceVal a α τ (cutU T) * faceVal b β τ ((cutV T).erase c))
        = ∑ c ∈ cutV T, (-1 : K) ^ ((cutU T).card - 1 + cutExp T + cutRank (cutV T) c)
            * (faceVal a α τ (cutU T) * faceVal b β τ ((cutV T).erase c)) :=
      Finset.sum_sdiff (subset_cutV T)
    rw [← hsU, ← hsV]
    ring
  -- Step 4: the leftover reindexes to one-point cuts and telescopes.
  have hmerge : ∀ T ∈ cutIndex 2 (n + 1),
      ((∑ c ∈ T, (-1 : K) ^ (cutExp T + cutRank (cutU T) c)
            * (faceVal a α τ ((cutU T).erase c) * faceVal b β τ (cutV T)))
        + ∑ c ∈ T, (-1 : K) ^ ((cutU T).card - 1 + cutExp T + cutRank (cutV T) c)
            * (faceVal a α τ (cutU T) * faceVal b β τ ((cutV T).erase c)))
      = ∑ c ∈ T, ((-1 : K) ^ (cutExp (insert c (T.erase c))
              + cutRank (cutU (insert c (T.erase c))) c)
            * (faceVal a α τ ((cutU (insert c (T.erase c))).erase c)
              * faceVal b β τ (cutV (insert c (T.erase c))))
          + (-1 : K) ^ ((cutU (insert c (T.erase c))).card - 1
              + cutExp (insert c (T.erase c)) + cutRank (cutV (insert c (T.erase c))) c)
            * (faceVal a α τ (cutU (insert c (T.erase c)))
              * faceVal b β τ ((cutV (insert c (T.erase c))).erase c))) := by
    intro T _
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [Finset.insert_erase hc]
  have hleft : (∑ T ∈ cutIndex 2 (n + 1),
        ((∑ c ∈ T, (-1 : K) ^ (cutExp T + cutRank (cutU T) c)
              * (faceVal a α τ ((cutU T).erase c) * faceVal b β τ (cutV T)))
          + ∑ c ∈ T, (-1 : K) ^ ((cutU T).card - 1 + cutExp T + cutRank (cutV T) c)
              * (faceVal a α τ (cutU T) * faceVal b β τ ((cutV T).erase c))))
      = ∑ S ∈ cutIndex 1 (n + 1),
          ((-1 : K) ^ (n + 2 + 1) * (faceVal a α τ (cutU S) * faceVal b β τ (cutV S))
            - (-1 : K) ^ (n + 2 + (n + 2) * ((cutU S).card - 1) + 1)
                * (faceVal a α τ (cutV S) * faceVal b β τ (cutU S))) := by
    rw [Finset.sum_congr rfl hmerge,
      sum_cutIndex_succ_erase 1 (n + 1) (fun S c =>
        (-1 : K) ^ (cutExp (insert c S) + cutRank (cutU (insert c S)) c)
            * (faceVal a α τ ((cutU (insert c S)).erase c) * faceVal b β τ (cutV (insert c S)))
          + (-1 : K) ^ ((cutU (insert c S)).card - 1 + cutExp (insert c S)
              + cutRank (cutV (insert c S)) c)
            * (faceVal a α τ (cutU (insert c S))
              * faceVal b β τ ((cutV (insert c S)).erase c)))]
    refine Finset.sum_congr rfl fun S hS => ?_
    obtain ⟨s, rfl⟩ := Finset.card_eq_one.1 (card_of_mem_cutIndex hS)
    rw [card_cutU_singleton s, Nat.add_sub_cancel]
    exact cut_insert_cancel_signed (fun A B => faceVal a α τ A * faceVal b β τ B) s
  rw [Finset.sum_congr rfl step3, Finset.sum_sub_distrib, Finset.sum_add_distrib, hleft]

/-! ## 4. The coboundary formula -/

/-- **Steenrod's cup-1 coboundary formula over any commutative ring.**  Every term lives
at a literal degree; nothing is transported along a degree equality.  The signs were
derived by an exact linear solve and verified in closed form
(`scratch/sp-cupone/cupone_signs.py`, `cupone_verify.py`). -/
theorem cochainCupOne_coboundary {K : Type} [CommRing K] {X : TopCat.{0}} (a b n : ℕ)
    (α : singularCochainGroup K X a) (β : singularCochainGroup K X b) :
    cochainCoboundary K X n (cochainCupOne a b n α β)
      = cochainCupOne (a + 1) b (n + 1) (cochainCoboundary K X a α) β
        + (-1 : K) ^ a • cochainCupOne a (b + 1) (n + 1) α (cochainCoboundary K X b β)
        + (-1 : K) ^ n • cochainCupI 0 a b (n + 1) α β
        + (-1 : K) ^ (a + b + a * b) • cochainCupI 0 b a (n + 1) β α := by
  classical
  apply cochain_ext
  intro τ
  rw [cochainEval_add, cochainEval_add, cochainEval_add, cochainEval_smul, cochainEval_smul,
    cochainEval_smul]
  have hlhs : cochainEval (n + 1) (cochainCoboundary K X n (cochainCupOne a b n α β)) τ
      = ∑ k : Fin (n + 2), ∑ S ∈ cutIndex 2 n,
          (-1 : K) ^ (k : ℕ) * (cupOneSign K S *
            (faceVal a α τ ((cutU (S.map (Fin.succAboveOrderEmb k).toEmbedding)).erase k)
              * faceVal b β τ
                  ((cutV (S.map (Fin.succAboveOrderEmb k).toEmbedding)).erase k))) := by
    rw [cochainCoboundary_eval]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [cochainCupOne_eval, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [faceVal_faceSimplex a n α k τ (cutU S), faceVal_faceSimplex b n β k τ (cutV S),
      cutU_map_succAbove k S, cutV_map_succAbove k S]
  have hT1 : cochainEval (n + 1)
        (cochainCupOne (a + 1) b (n + 1) (cochainCoboundary K X a α) β) τ
      = ∑ T ∈ cutIndex 2 (n + 1), ∑ c ∈ cutU T,
          (-1 : K) ^ (cutExp T + cutRank (cutU T) c)
            * (faceVal a α τ ((cutU T).erase c) * faceVal b β τ (cutV T)) := by
    rw [cochainCupOne_eval]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [faceVal_coboundary_signed a n α τ (cutU T), Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [cupOneSign_def, pow_add]
    ring
  have hT2 : (-1 : K) ^ a * cochainEval (n + 1)
        (cochainCupOne a (b + 1) (n + 1) α (cochainCoboundary K X b β)) τ
      = ∑ T ∈ cutIndex 2 (n + 1), ∑ c ∈ cutV T,
          (-1 : K) ^ ((cutU T).card - 1 + cutExp T + cutRank (cutV T) c)
            * (faceVal a α τ (cutU T) * faceVal b β τ ((cutV T).erase c)) := by
    rw [cochainCupOne_eval, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [faceVal_coboundary_signed b n β τ (cutV T), Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hcard : (cutU T).card = a + 1
    · rw [hcard, Nat.add_sub_cancel, cupOneSign_def, pow_add, pow_add]
      ring
    · rw [faceVal_of_card_ne α τ hcard]
      ring
  have hT3 : cochainEval (n + 1) (cochainCupI 0 a b (n + 1) α β) τ
      = ∑ S ∈ cutIndex 1 (n + 1), faceVal a α τ (cutU S) * faceVal b β τ (cutV S) :=
    cochainCupI_eval 0 a b (n + 1) α β τ
  have hT4 : cochainEval (n + 1) (cochainCupI 0 b a (n + 1) β α) τ
      = ∑ S ∈ cutIndex 1 (n + 1), faceVal a α τ (cutV S) * faceVal b β τ (cutU S) := by
    rw [cochainCupI_eval]
    exact Finset.sum_congr rfl fun S _ => mul_comm _ _
  have hlow : (∑ S ∈ cutIndex 1 (n + 1),
        ((-1 : K) ^ (n + 2 + 1) * (faceVal a α τ (cutU S) * faceVal b β τ (cutV S))
          - (-1 : K) ^ (n + 2 + (n + 2) * ((cutU S).card - 1) + 1)
              * (faceVal a α τ (cutV S) * faceVal b β τ (cutU S))))
      = - ((-1 : K) ^ n * (∑ S ∈ cutIndex 1 (n + 1),
                faceVal a α τ (cutU S) * faceVal b β τ (cutV S))
          + (-1 : K) ^ (a + b + a * b) * (∑ S ∈ cutIndex 1 (n + 1),
                faceVal a α τ (cutV S) * faceVal b β τ (cutU S))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun S hS => ?_
    obtain ⟨s, rfl⟩ := Finset.card_eq_one.1 (card_of_mem_cutIndex hS)
    have hc1 : (-1 : K) ^ (n + 2 + 1) = - (-1 : K) ^ n := by
      rw [pow_add, pow_add]
      ring
    rw [card_cutU_singleton s, Nat.add_sub_cancel, hc1]
    by_cases hY1 : (cutU ({s} : Finset (Fin (n + 2)))).card = b + 1
    · by_cases hY2 : (cutV ({s} : Finset (Fin (n + 2)))).card = a + 1
      · have hs : s.val = b := by
          rw [card_cutU_singleton s] at hY1
          omega
        have hab : a + b = n + 1 := by
          have hsum := cutU_card_add_cutV_card ({s} : Finset (Fin (n + 2)))
          rw [hY1, hY2, Finset.card_singleton] at hsum
          omega
        have hc2 : (-1 : K) ^ (n + 2 + (n + 2) * s.val + 1) = (-1 : K) ^ (a + b + a * b) := by
          refine neg_one_pow_congr_mod_two (K := K) ?_
          have hn : n + 2 = a + b + 1 := by omega
          rw [hs, hn]
          have hexp : (a + b + 1) * b = a * b + b * b + b := by ring
          have hsq := mul_self_mod_two b
          omega
        rw [hc2]
        ring
      · rw [faceVal_of_card_ne α τ hY2]
        ring
    · rw [faceVal_of_card_ne β τ hY1]
      ring
  rw [hlhs, cut_coboundary_master_signed a b α β τ, hlow, ← hT1, ← hT2, hT3, hT4]
  ring

end

end CharClass
end GroupApproximation
