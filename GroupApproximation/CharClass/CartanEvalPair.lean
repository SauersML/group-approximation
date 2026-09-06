import GroupApproximation.CharClass.CartanEvalCocycle
import GroupApproximation.CharClass.SteenrodPairing
import GroupApproximation.CharClass.SteenrodPairCell

/-!
# Pairing two cochains against the pair index

`cc-steenrod`'s `pairEval` pairs two cochains against one *fixed* bidegree of the
tensor square.  The pair index carries a *varying* bidegree, because that is what
the differential moves.  This file is the bridge: one functional on the whole
degree-`k` module, agreeing with `pairEval` on the matching bidegree and
vanishing on every other.

Nothing here needs a degree side-condition, because `evAt` already extends a
cochain to every degree by zero.  A basis element of the wrong bidegree is killed
by the factor whose degree is wrong, and a bidegree that does not sum to `k` is
killed by `padIdx` before the functional sees it.

## Main results

* `pairEvalIdx` — the functional.
* `pairEvalIdx_cellPair_self` — on the matching bidegree it is `pairEval`.
* `pairEvalIdx_cellPair_of_ne_left`, `..._of_ne_right` — every other bidegree
  contributes nothing.
* `pairEvalIdx_phiPair` — **the bridge**: pairing two cochains against Steenrod's
  diagonal is evaluating their cup-`i` product.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

variable {X : TopCat.{0}}

/-! ## 1. The functional -/

/-- The value on a basis element of the pair index: the product of the two
values, and `0` unless the bidegree matches the two cochains. -/
noncomputable def pairEvalGen (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (k : ℕ) (u : Steenrod.PairIdx X k) : ZMod 2 :=
  evAt X p α u.1.val.1 u.2.1 * evAt X q β u.1.val.2 u.2.2

/-- **Pairing two cochains against the whole degree-`k` module.** -/
noncomputable def pairEvalIdx (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (k : ℕ) : (Steenrod.PairIdx X k →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  Finsupp.linearCombination (ZMod 2) (pairEvalGen X p q α β k)

@[simp] theorem pairEvalIdx_single (p q k : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (u : Steenrod.PairIdx X k) (c : ZMod 2) :
    pairEvalIdx X p q α β k (Finsupp.single u c) = c * pairEvalGen X p q α β k u := by
  unfold pairEvalIdx
  rw [Finsupp.linearCombination_single, smul_eq_mul]

/-! ## 2. Only the matching bidegree survives -/

theorem pairEvalIdx_padIdx_self (p q k : ℕ) (h : p + q = k)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (pr : singularSimplices X p × singularSimplices X q) :
    pairEvalIdx X p q α β k (Steenrod.padIdx X k p q pr)
      = cochainEval p α pr.1 * cochainEval q β pr.2 := by
  rw [Steenrod.padIdx_of_eq h, pairEvalIdx_single, one_mul]
  show evAt X p α p pr.1 * evAt X q β q pr.2 = _
  rw [evAt_self, evAt_self]

theorem pairEvalIdx_padIdx_of_ne_left (p q k a b : ℕ) (ha : a ≠ p)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (pr : singularSimplices X a × singularSimplices X b) :
    pairEvalIdx X p q α β k (Steenrod.padIdx X k a b pr) = 0 := by
  by_cases h : a + b = k
  · rw [Steenrod.padIdx_of_eq h, pairEvalIdx_single, one_mul]
    show evAt X p α a pr.1 * evAt X q β b pr.2 = 0
    rw [evAt_of_ne X p α a ha, zero_mul]
  · rw [Steenrod.padIdx_of_ne h, map_zero]

theorem pairEvalIdx_padIdx_of_ne_right (p q k a b : ℕ) (hb : b ≠ q)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (pr : singularSimplices X a × singularSimplices X b) :
    pairEvalIdx X p q α β k (Steenrod.padIdx X k a b pr) = 0 := by
  by_cases h : a + b = k
  · rw [Steenrod.padIdx_of_eq h, pairEvalIdx_single, one_mul]
    show evAt X p α a pr.1 * evAt X q β b pr.2 = 0
    rw [evAt_of_ne X q β b hb, mul_zero]
  · rw [Steenrod.padIdx_of_ne h, map_zero]

/-- **On the matching bidegree the functional is `cc-steenrod`'s `pairEval`.** -/
theorem pairEvalIdx_cellPair_self (p q k : ℕ) (h : p + q = k)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (z : tensorTwo X p q) :
    pairEvalIdx X p q α β k (Steenrod.cellPair X k p q z)
      = Steenrod.pairEval p q α β z := by
  induction z using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero]
  | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]
  | single pr c =>
      rw [Steenrod.cellPair_single, map_smul, smul_eq_mul,
        pairEvalIdx_padIdx_self p q k h α β pr, Steenrod.pairEval_single]

/-- Every other bidegree contributes nothing. -/
theorem pairEvalIdx_cellPair_of_ne_left (p q k a b : ℕ) (ha : a ≠ p)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (z : tensorTwo X a b) :
    pairEvalIdx X p q α β k (Steenrod.cellPair X k a b z) = 0 := by
  induction z using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add u v hu hv => rw [map_add, map_add, hu, hv, add_zero]
  | single pr c =>
      rw [Steenrod.cellPair_single, map_smul, smul_eq_mul,
        pairEvalIdx_padIdx_of_ne_left p q k a b ha α β pr, mul_zero]

theorem pairEvalIdx_cellPair_of_ne_right (p q k a b : ℕ) (hb : b ≠ q)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (z : tensorTwo X a b) :
    pairEvalIdx X p q α β k (Steenrod.cellPair X k a b z) = 0 := by
  induction z using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add u v hu hv => rw [map_add, map_add, hu, hv, add_zero]
  | single pr c =>
      rw [Steenrod.cellPair_single, map_smul, smul_eq_mul,
        pairEvalIdx_padIdx_of_ne_right p q k a b hb α β pr, mul_zero]

/-! ## 3. The bridge -/

/-- One bidegree of the diagonal, paired against two cochains of that bidegree. -/
theorem pairEvalIdx_phiCell_self (k i p q : ℕ) (h : p + q = k)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    {N : ℕ} (σ : singularSimplices X N) :
    pairEvalIdx X p q α β k (Steenrod.phiCell X k i p q σ)
      = cochainEval N (cochainCupI i p q N α β) σ := by
  show pairEvalIdx X p q α β k (Steenrod.cellPair X k p q (steenrodDiag i p q σ)) = _
  rw [pairEvalIdx_cellPair_self p q k h α β, Steenrod.pairEval_steenrodDiag]

/-- **The bridge.**  Pairing two cochains against Steenrod's diagonal on the pair
index is evaluating their cup-`i` product.  Only the bidegree of the two cochains
survives the sum over bidegrees. -/
theorem pairEvalIdx_phiPair (k : ℕ) (n : Fin (k + 1)) (p q : ℕ) (h : p + q = k)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (σ : singularSimplices X n.val) :
    pairEvalIdx X p q α β k (Steenrod.phiPair X k ⟨n, σ⟩)
      = cochainEval n.val (cochainCupI (k - n.val) p q n.val α β) σ := by
  rw [Steenrod.phiPair_eq, map_sum]
  refine (Finset.sum_eq_single p ?_ ?_).trans ?_
  · intro a _ hne
    show pairEvalIdx X p q α β k
      (Steenrod.cellPair X k a (k - a) (steenrodDiag (k - n.val) a (k - a) σ)) = 0
    exact pairEvalIdx_cellPair_of_ne_left p q k a (k - a) hne α β _
  · intro hp
    exact absurd (Finset.mem_range.mpr (show p < k + 1 by omega)) hp
  · rw [Steenrod.phiCell_congr_b (X := X) k (k - n.val) p σ (show k - p = q by omega)]
    exact pairEvalIdx_phiCell_self k (k - n.val) p q h α β σ

end

end GroupApproximation.CharClass
