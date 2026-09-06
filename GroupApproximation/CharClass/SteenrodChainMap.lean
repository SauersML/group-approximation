import GroupApproximation.CharClass.SteenrodPairCell

/-!
# Steenrod's diagonal is a chain map

This is the identity the whole equivariant comparison rests on:

```text
∂ Φ(e_i ⊗ σ) = Φ(e_{i-1} ⊗ σ) + T Φ(e_{i-1} ⊗ σ) + Φ(e_i ⊗ ∂σ)
```

Read on a generator of `(W ⊗ S(X))_{k+1}`, the right-hand side is exactly the
value of the source differential of `CartanDiagonalModule.lean`, whose two halves
are multiplication by `1 + t` and the simplicial boundary.  So the equation says
`Φ ∘ d = ∂ ∘ Φ`.

## The three cases, and why there are exactly three

A generator is a simplex degree `n ≤ k+1` together with an `n`-simplex.  The
`(1 + t)` half of the source differential is absent when `n = k+1` (the `W`-index
is already `0`), and the boundary half is absent when `n = 0`.  That is a
`Fin.cases` on `n` followed by a `Fin.lastCases` on its predecessor, and it gives:

* `n = 0` — both sides vanish.  The left side because a `0`-simplex has no cut
  with `k+2` cut points; the right side because `Φ(e_k ⊗ x) + T Φ(e_k ⊗ x)` is
  either `0 + 0` (for `k ≥ 1`, again for want of cuts) or `x⊗x + x⊗x` (for
  `k = 0`, where the swap fixes the diagonal).
* `1 ≤ n ≤ k` — the general case, `steenrodDiag_boundary'`.
* `n = k+1` — the Alexander–Whitney end, `steenrodDiag_boundary_zero'`, where the
  two low terms are absent and `Φ` is a chain map on the nose.

The three case lemmas take their cut indices as *abstract naturals* with an
equation, rather than as the `Fin.val` expressions the case analysis produces.
That is what keeps the arithmetic (`k + 1 - (k + 1) = 0`, and
`k - j = (k - (j+1)) + 1` for `j < k`) out of the mathematics and inside a single
`omega` call each.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial SimplexCategory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

variable {X : TopCat.{0}}

/-! ## 1. The left-hand side, reduced -/

theorem sum_dTgtL (k I : ℕ) {N : ℕ} (σ : singularSimplices X N) :
    (∑ a ∈ Finset.range (k + 1 + 1), dTgtL X k (phiCell X (k + 1) I a (k + 1 - a) σ))
      = ∑ a ∈ Finset.range (k + 1),
          cellPair X k a (k - a) (tenBdL X a (k - a) (steenrodDiag I (a + 1) (k - a) σ)) := by
  rw [Finset.sum_range_succ']
  have hzero : dTgtL X k (phiCell X (k + 1) I 0 (k + 1 - 0) σ) = 0 :=
    dTgtL_cellPair_zero k (k + 1 - 0) (steenrodDiag I 0 (k + 1 - 0) σ)
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [phiCell_congr_b (k + 1) I (a + 1) σ (show k + 1 - (a + 1) = k - a by omega)]
  exact dTgtL_cellPair k a (k - a) (steenrodDiag I (a + 1) (k - a) σ)

theorem sum_dTgtR (k I : ℕ) {N : ℕ} (σ : singularSimplices X N) :
    (∑ a ∈ Finset.range (k + 1 + 1), dTgtR X k (phiCell X (k + 1) I a (k + 1 - a) σ))
      = ∑ a ∈ Finset.range (k + 1),
          cellPair X k a (k - a) (tenBdR X a (k - a) (steenrodDiag I a (k - a + 1) σ)) := by
  rw [Finset.sum_range_succ]
  have htop : dTgtR X k (phiCell X (k + 1) I (k + 1) (k + 1 - (k + 1)) σ) = 0 := by
    rw [phiCell_congr_b (k + 1) I (k + 1) σ (show k + 1 - (k + 1) = 0 by omega)]
    exact dTgtR_cellPair_zero k (k + 1) (steenrodDiag I (k + 1) 0 σ)
  rw [htop, add_zero]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.mem_range] at ha
  rw [phiCell_congr_b (k + 1) I a σ (show k + 1 - a = k - a + 1 by omega)]
  exact dTgtR_cellPair k a (k - a) (steenrodDiag I a (k - a + 1) σ)

/-- **The differential of `Φ(e_i ⊗ σ)`, bidegree by bidegree.**  Both halves of
the target differential land in the same `k+1` bidegrees, with the left half
shifted by one. -/
theorem dTgt_phiSum (k I : ℕ) {N : ℕ} (σ : singularSimplices X N) :
    dTgt X (ZMod 2) k (∑ a ∈ Finset.range (k + 1 + 1), phiCell X (k + 1) I a (k + 1 - a) σ)
      = ∑ a ∈ Finset.range (k + 1),
          cellPair X k a (k - a)
            (tenBdL X a (k - a) (steenrodDiag I (a + 1) (k - a) σ)
              + tenBdR X a (k - a) (steenrodDiag I a (k - a + 1) σ)) := by
  rw [dTgt_eq_add, map_sum, map_sum, sum_dTgtL, sum_dTgtR, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact (map_add (cellPair X k a (k - a)) _ _).symm

/-! ## 2. Two degenerate values of the diagonal -/

theorem tensorSwap_zero (a b : ℕ) : tensorSwap (X := X) a b 0 = 0 := by
  unfold tensorSwap
  exact Finsupp.mapDomain_zero

/-- On a `0`-simplex the diagonal is `x ⊗ x`, which the swap fixes. -/
theorem tensorSwap_steenrodDiag_degree_zero (σ : singularSimplices X 0) :
    tensorSwap 0 0 (steenrodDiag 0 0 0 σ) = steenrodDiag 0 0 0 σ := by
  rw [steenrodDiag_degree_zero σ]
  unfold tensorSwap
  exact Finsupp.mapDomain_single

/-! ## 3. The three cases -/

/-- **Simplex degree `0`.**  Both sides vanish. -/
theorem chainmap_case_zero (k I J : ℕ) {N : ℕ} (hN : N = 0) (hI : I = k + 1) (hJ : J = k)
    (σ : singularSimplices X N) :
    (∑ a ∈ Finset.range (k + 1), cellPair X k a (k - a)
        (tenBdL X a (k - a) (steenrodDiag I (a + 1) (k - a) σ)
          + tenBdR X a (k - a) (steenrodDiag I a (k - a + 1) σ)))
      = (∑ a ∈ Finset.range (k + 1), phiCell X k J a (k - a) σ)
        + swapEnd X k (∑ a ∈ Finset.range (k + 1), phiCell X k J a (k - a) σ) := by
  subst hN
  rw [hI, hJ]
  have hLzero : (∑ a ∈ Finset.range (k + 1), cellPair X k a (k - a)
      (tenBdL X a (k - a) (steenrodDiag (k + 1) (a + 1) (k - a) σ)
        + tenBdR X a (k - a) (steenrodDiag (k + 1) a (k - a + 1) σ))) = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [steenrodDiag_eq_zero_of_lt (k + 1) (a + 1) (k - a) σ (by omega),
      steenrodDiag_eq_zero_of_lt (k + 1) a (k - a + 1) σ (by omega), map_zero, map_zero,
      add_zero]
    exact map_zero _
  have hZY : ∀ a ∈ Finset.range (k + 1),
      phiCellSwap X k k a (k - a) σ = phiCell X k k a (k - a) σ := by
    intro a ha
    rw [Finset.mem_range] at ha
    rcases Nat.eq_zero_or_pos k with hk | hk
    · have ha0 : a = 0 := by omega
      subst hk
      subst ha0
      show cellPair X 0 0 0 (tensorSwap 0 0 (steenrodDiag 0 0 0 σ))
          = cellPair X 0 0 0 (steenrodDiag 0 0 0 σ)
      exact congrArg (fun z => cellPair X 0 0 0 z) (tensorSwap_steenrodDiag_degree_zero σ)
    · show cellPair X k a (k - a) (tensorSwap (k - a) a (steenrodDiag k (k - a) a σ))
          = cellPair X k a (k - a) (steenrodDiag k a (k - a) σ)
      rw [steenrodDiag_eq_zero_of_lt k (k - a) a σ (by omega),
        steenrodDiag_eq_zero_of_lt k a (k - a) σ (by omega)]
      exact congrArg (fun z => cellPair X k a (k - a) z) (tensorSwap_zero (k - a) a)
  rw [hLzero, swapEnd_phiSum, Finset.sum_congr rfl hZY]
  exact (pair_add_self _).symm

/-- **The Alexander–Whitney end.**  The `(1 + t)` half of the source differential
is absent, and `Φ` is a chain map on the nose. -/
theorem chainmap_case_last (k M I J : ℕ) (hI : I = 0) (hJ : J = 0)
    (σ : singularSimplices X (M + 1)) :
    (∑ a ∈ Finset.range (k + 1), cellPair X k a (k - a)
        (tenBdL X a (k - a) (steenrodDiag I (a + 1) (k - a) σ)
          + tenBdR X a (k - a) (steenrodDiag I a (k - a + 1) σ)))
      = ∑ jj : Fin (M + 2), ∑ a ∈ Finset.range (k + 1),
          phiCell X k J a (k - a) (faceSimplex X M jj σ) := by
  rw [hI, hJ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hmap : (∑ jj : Fin (M + 2), phiCell X k 0 a (k - a) (faceSimplex X M jj σ))
      = cellPair X k a (k - a)
          (∑ jj : Fin (M + 2), steenrodDiag 0 a (k - a) (faceSimplex X M jj σ)) :=
    (map_sum (cellPair X k a (k - a))
      (fun jj => steenrodDiag 0 a (k - a) (faceSimplex X M jj σ)) Finset.univ).symm
  rw [hmap]
  exact congrArg (fun z => cellPair X k a (k - a) z)
    (steenrodDiag_boundary_zero' a (k - a) M σ).symm

/-- **The general case.**  The two low terms of the boundary identity are
`Φ(e_{i} ⊗ σ)` and `T Φ(e_{i} ⊗ σ)`, and they appear twice, so they cancel in
characteristic two. -/
theorem chainmap_case_mid (k i M I J : ℕ) (hI : I = i + 1) (hJ : J = i + 1)
    (σ : singularSimplices X (M + 1)) :
    (∑ a ∈ Finset.range (k + 1), cellPair X k a (k - a)
        (tenBdL X a (k - a) (steenrodDiag I (a + 1) (k - a) σ)
          + tenBdR X a (k - a) (steenrodDiag I a (k - a + 1) σ)))
      = ((∑ a ∈ Finset.range (k + 1), phiCell X k i a (k - a) σ)
          + swapEnd X k (∑ a ∈ Finset.range (k + 1), phiCell X k i a (k - a) σ))
        + ∑ jj : Fin (M + 2), ∑ a ∈ Finset.range (k + 1),
            phiCell X k J a (k - a) (faceSimplex X M jj σ) := by
  rw [hI, hJ]
  have hS : (∑ jj : Fin (M + 2), ∑ a ∈ Finset.range (k + 1),
        phiCell X k (i + 1) a (k - a) (faceSimplex X M jj σ))
      = (∑ a ∈ Finset.range (k + 1), cellPair X k a (k - a)
            (tenBdL X a (k - a) (steenrodDiag (i + 1) (a + 1) (k - a) σ)
              + tenBdR X a (k - a) (steenrodDiag (i + 1) a (k - a + 1) σ)))
        + ((∑ a ∈ Finset.range (k + 1), phiCell X k i a (k - a) σ)
            + ∑ a ∈ Finset.range (k + 1), phiCellSwap X k i a (k - a) σ) := by
    rw [Finset.sum_comm, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hmap : (∑ jj : Fin (M + 2), phiCell X k (i + 1) a (k - a) (faceSimplex X M jj σ))
        = cellPair X k a (k - a)
            (∑ jj : Fin (M + 2), steenrodDiag (i + 1) a (k - a) (faceSimplex X M jj σ)) :=
      (map_sum (cellPair X k a (k - a))
        (fun jj => steenrodDiag (i + 1) a (k - a) (faceSimplex X M jj σ)) Finset.univ).symm
    rw [hmap, steenrodDiag_boundary' i a (k - a) M σ, map_add, map_add, add_assoc]
    rfl
  have hfin : ∀ u v w : PairIdx X k →₀ ZMod 2, (v + w) + (u + (v + w)) = u := by
    intro u v w
    have h1 : (v + w) + (u + (v + w)) = u + ((v + v) + (w + w)) := by abel
    rw [h1, pair_add_self, pair_add_self, add_zero, add_zero]
  rw [swapEnd_phiSum, hS]
  exact (hfin _ _ _).symm

/-! ## 4. The source differential, transported to the target -/

/-- The value of `Φ` on the `(1 + t)` half of the source differential. -/
def phiOfW (X : TopCat.{0}) (k : ℕ) :
    ∀ n : Fin (k + 2), singularSimplices X n.val → (PairIdx X k →₀ ZMod 2) :=
  Fin.lastCases
    (motive := fun n : Fin (k + 2) => singularSimplices X n.val → (PairIdx X k →₀ ZMod 2))
    (fun _ => 0)
    (fun j σ => phiPair X k ⟨j, σ⟩ + swapEnd X k (phiPair X k ⟨j, σ⟩))

@[simp] theorem phiOfW_last (X : TopCat.{0}) (k : ℕ)
    (σ : singularSimplices X (Fin.last (k + 1)).val) :
    phiOfW X k (Fin.last (k + 1)) σ = 0 := by
  rw [phiOfW, Fin.lastCases_last]

@[simp] theorem phiOfW_castSucc (X : TopCat.{0}) (k : ℕ) (j : Fin (k + 1))
    (σ : singularSimplices X (Fin.castSucc j).val) :
    phiOfW X k (Fin.castSucc j) σ
      = phiPair X k ⟨j, σ⟩ + swapEnd X k (phiPair X k ⟨j, σ⟩) := by
  rw [phiOfW, Fin.lastCases_castSucc]

/-- The value of `Φ` on the simplicial half of the source differential. -/
def phiOfS (X : TopCat.{0}) (k : ℕ) :
    ∀ n : Fin (k + 2), singularSimplices X n.val → (PairIdx X k →₀ ZMod 2) :=
  Fin.cases
    (motive := fun n : Fin (k + 2) => singularSimplices X n.val → (PairIdx X k →₀ ZMod 2))
    (fun _ => 0)
    (fun m σ => ∑ jj : Fin (m.val + 2), phiPair X k ⟨m, faceSimplex X m.val jj σ⟩)

@[simp] theorem phiOfS_zero (X : TopCat.{0}) (k : ℕ)
    (σ : singularSimplices X (0 : Fin (k + 2)).val) : phiOfS X k 0 σ = 0 := by
  rw [phiOfS, Fin.cases_zero]

@[simp] theorem phiOfS_succ (X : TopCat.{0}) (k : ℕ) (m : Fin (k + 1))
    (σ : singularSimplices X (Fin.succ m).val) :
    phiOfS X k (Fin.succ m) σ
      = ∑ jj : Fin (m.val + 2), phiPair X k ⟨m, faceSimplex X m.val jj σ⟩ := by
  rw [phiOfS, Fin.cases_succ]

/-! ## 5. The chain-map identity on a generator -/

/-- **Steenrod's diagonal is a chain map**, on a generator of `(W ⊗ S(X))_{k+1}`.
The right-hand side is the value of `Φ` on the source differential: the
`(1 + t)` half and the boundary half. -/
theorem dTgt_phiPair (X : TopCat.{0}) (k : ℕ) (n : Fin (k + 2))
    (σ : singularSimplices X n.val) :
    dTgt X (ZMod 2) k (phiPair X (k + 1) ⟨n, σ⟩) = phiOfW X k n σ + phiOfS X k n σ := by
  revert σ
  induction n using Fin.cases with
  | zero =>
      intro σ
      have hW : phiOfW X k (0 : Fin (k + 2)) σ
          = phiPair X k ⟨(0 : Fin (k + 1)), σ⟩
            + swapEnd X k (phiPair X k ⟨(0 : Fin (k + 1)), σ⟩) :=
        phiOfW_castSucc X k 0 σ
      have hS : phiOfS X k (0 : Fin (k + 2)) σ = 0 := phiOfS_zero X k σ
      rw [phiPair_eq X (k + 1) 0 σ, dTgt_phiSum, hW, hS, add_zero, phiPair_eq X k 0 σ]
      exact chainmap_case_zero k _ _ (by simp) (by simp) (by simp) σ
  | succ m =>
      induction m using Fin.lastCases with
      | last =>
          intro σ
          have hW : phiOfW X k (Fin.succ (Fin.last k)) σ = 0 := phiOfW_last X k σ
          have hS : phiOfS X k (Fin.succ (Fin.last k)) σ
              = ∑ jj : Fin ((Fin.last k).val + 2),
                  phiPair X k ⟨Fin.last k, faceSimplex X (Fin.last k).val jj σ⟩ :=
            phiOfS_succ X k (Fin.last k) σ
          have hinner : ∀ jj : Fin ((Fin.last k).val + 2),
              phiPair X k ⟨Fin.last k, faceSimplex X (Fin.last k).val jj σ⟩
                = ∑ a ∈ Finset.range (k + 1),
                    phiCell X k (k - (Fin.last k).val) a (k - a)
                      (faceSimplex X (Fin.last k).val jj σ) :=
            fun jj => phiPair_eq X k (Fin.last k) _
          rw [phiPair_eq X (k + 1) (Fin.succ (Fin.last k)) σ, dTgt_phiSum, hW, hS, zero_add,
            Finset.sum_congr rfl (fun jj (_ : jj ∈ Finset.univ) => hinner jj)]
          exact chainmap_case_last k (Fin.last k).val _ _ (by simp) (by simp) σ
      | cast j =>
          intro σ
          have hjk : j.val < k := j.isLt
          have hv1 : (Fin.succ (Fin.castSucc j)).val = j.val + 1 := rfl
          have hv2 : (Fin.succ j).val = j.val + 1 := rfl
          have hv3 : (Fin.castSucc j).val = j.val := rfl
          have hW : phiOfW X k (Fin.succ (Fin.castSucc j)) σ
              = phiPair X k ⟨Fin.succ j, σ⟩ + swapEnd X k (phiPair X k ⟨Fin.succ j, σ⟩) :=
            phiOfW_castSucc X k (Fin.succ j) σ
          have hS : phiOfS X k (Fin.succ (Fin.castSucc j)) σ
              = ∑ jj : Fin ((Fin.castSucc j).val + 2),
                  phiPair X k ⟨Fin.castSucc j, faceSimplex X (Fin.castSucc j).val jj σ⟩ :=
            phiOfS_succ X k (Fin.castSucc j) σ
          have hinner : ∀ jj : Fin ((Fin.castSucc j).val + 2),
              phiPair X k ⟨Fin.castSucc j, faceSimplex X (Fin.castSucc j).val jj σ⟩
                = ∑ a ∈ Finset.range (k + 1),
                    phiCell X k (k - (Fin.castSucc j).val) a (k - a)
                      (faceSimplex X (Fin.castSucc j).val jj σ) :=
            fun jj => phiPair_eq X k (Fin.castSucc j) _
          rw [phiPair_eq X (k + 1) (Fin.succ (Fin.castSucc j)) σ, dTgt_phiSum, hW, hS,
            phiPair_eq X k (Fin.succ j) σ,
            Finset.sum_congr rfl (fun jj (_ : jj ∈ Finset.univ) => hinner jj)]
          exact chainmap_case_mid k (k - (Fin.succ j).val) (Fin.castSucc j).val _ _
            (by rw [hv1, hv2]; omega) (by rw [hv3, hv2]; omega) σ

end

end Steenrod
end CharClass
end GroupApproximation
