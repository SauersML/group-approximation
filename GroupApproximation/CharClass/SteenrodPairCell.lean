import GroupApproximation.CharClass.SteenrodPairBoundary
import GroupApproximation.CharClass.SteenrodDiagonalPhi

/-!
# One bidegree of the target, as a total operation

`phiPair` is a sum over bidegrees, and the target's differential moves a
bidegree.  Comparing the two therefore means summing over bidegrees on both
sides, and the two sums have different lengths: `phiPair` in degree `k+1` runs
over `k+2` bidegrees, its differential over `k+1`.

Indexing those sums by `Fin` makes every reindexing step a transport.  So the
bidegree here is a **pair of plain naturals with no constraint**, and the
constraint is absorbed into the injection: `padIdx` is `0` unless the two
degrees sum to the total one, exactly as `faceVal` is `0` unless the vertex set
has the right size.  Then every sum runs over `Finset.range`, the summand is a
function of a bare natural, and `Finset.sum_range_succ` and `Finset.sum_nbij'`
apply with no casts at all.

## Contents

* `padIdx`, `cellPair` — the totalised injection of one bidegree, and its
  linear extension.
* `phiPair_eq` — the published `phiPair` as a `Finset.range` sum of `phiCell`.
* `dTgtL`, `dTgtR` — the two halves of the target differential as global
  operators, with `dTgt_eq_add`.
* `dTgtL_cellPair`, `dTgtR_cellPair` — each half of the target differential is
  the corresponding half of the *bidegree* boundary, `tenBdL` and `tenBdR`.
  This is the bridge between `SteenrodPairBoundary.lean` and the differential
  `cc-cartan` consumes.
* `swapEnd_phiSum` — **the equivariance step**: the geometric swap on the whole
  degree-`k` module is the bidegree reversal `a ↦ k - a` composed with
  `tensorSwap` in each bidegree.  This is the only place `k - (k - a) = a` is
  used, and it is used on plain naturals, not inside a type.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial SimplexCategory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

variable {X : TopCat.{0}}

/-! ## 1. The totalised bidegree injection -/

/-- The basis element of `(S(X) ⊗ S(X))_k` given by a pair of simplices of
degrees `a` and `b`, and `0` unless `a + b = k`.  Totality here plays the same
role as it does for `faceVal`: it removes every degree side-condition from the
statements below. -/
def padIdx (X : TopCat.{0}) (k a b : ℕ)
    (p : singularSimplices X a × singularSimplices X b) : PairIdx X k →₀ ZMod 2 :=
  if h : a + b = k then Finsupp.single (⟨⟨(a, b), h⟩, p⟩ : PairIdx X k) 1 else 0

theorem padIdx_of_eq {k a b : ℕ} (h : a + b = k)
    (p : singularSimplices X a × singularSimplices X b) :
    padIdx X k a b p = Finsupp.single (⟨⟨(a, b), h⟩, p⟩ : PairIdx X k) 1 :=
  dif_pos h

theorem padIdx_of_ne {k a b : ℕ} (h : ¬ a + b = k)
    (p : singularSimplices X a × singularSimplices X b) : padIdx X k a b p = 0 :=
  dif_neg h

/-- One bidegree of `S(X) ⊗ S(X)`, injected into the degree-`k` module. -/
def cellPair (X : TopCat.{0}) (k a b : ℕ) :
    tensorTwo X a b →ₗ[ZMod 2] (PairIdx X k →₀ ZMod 2) :=
  Finsupp.linearCombination (ZMod 2) (padIdx X k a b)

theorem cellPair_single (k a b : ℕ) (p : singularSimplices X a × singularSimplices X b)
    (c : ZMod 2) : cellPair X k a b (Finsupp.single p c) = c • padIdx X k a b p := by
  unfold cellPair
  simp

theorem cellPair_single_one (k a b : ℕ)
    (p : singularSimplices X a × singularSimplices X b) :
    cellPair X k a b (Finsupp.single p 1) = padIdx X k a b p := by
  rw [cellPair_single]
  exact one_smul _ _

theorem cellPair_of_ne {k a b : ℕ} (h : ¬ a + b = k) (z : tensorTwo X a b) :
    cellPair X k a b z = 0 := by
  classical
  refine Finsupp.induction_linear z ?_ ?_ ?_
  · exact map_zero _
  · intro u v hu hv
    rw [map_add, hu, hv]
    exact add_zero _
  · intro p c
    rw [cellPair_single, padIdx_of_ne h]
    exact smul_zero c

theorem cellPair_of_eq {k a b : ℕ} (h : a + b = k) (z : tensorTwo X a b) :
    cellPair X k a b z
      = Finsupp.mapDomain (fun p => (⟨⟨(a, b), h⟩, p⟩ : PairIdx X k)) z := by
  classical
  refine Finsupp.induction_linear z ?_ ?_ ?_
  · rw [map_zero]
    exact Finsupp.mapDomain_zero.symm
  · intro u v hu hv
    rw [map_add, hu, hv]
    exact Finsupp.mapDomain_add.symm
  · intro p c
    rw [cellPair_single, padIdx_of_eq h, Finsupp.smul_single, smul_eq_mul, mul_one]
    exact Finsupp.mapDomain_single.symm

/-! ## 2. The published `phiPair` as a `range` sum -/

/-- One bidegree of `Φ(e_i ⊗ σ)`. -/
def phiCell (X : TopCat.{0}) (k i a b : ℕ) {N : ℕ} (σ : singularSimplices X N) :
    PairIdx X k →₀ ZMod 2 :=
  cellPair X k a b (steenrodDiag i a b σ)

theorem phiCell_congr_b (k i a : ℕ) {b b' N : ℕ} (σ : singularSimplices X N) (h : b = b') :
    phiCell X k i a b σ = phiCell X k i a b' σ := by
  subst h
  rfl

theorem phiCell_congr_i (k a b : ℕ) {i i' N : ℕ} (σ : singularSimplices X N) (h : i = i') :
    phiCell X k i a b σ = phiCell X k i' a b σ := by
  subst h
  rfl

theorem mapDomain_injectPair (X : TopCat.{0}) {k : ℕ} (a : Fin (k + 1))
    (z : tensorTwo X a.val (k - a.val)) :
    Finsupp.mapDomain (pairIndexToIdx X k) (injectPair X (ZMod 2) a z)
      = cellPair X k a.val (k - a.val) z := by
  have hid : Finsupp.mapRange (algebraMap (ZMod 2) (ZMod 2)) (map_zero _) z = z := by
    ext p
    rw [Finsupp.mapRange_apply]
    rfl
  have hcell : cellPair X k a.val (k - a.val) z
      = Finsupp.mapDomain
          (fun p => (⟨⟨(a.val, k - a.val), by omega⟩, p⟩ : PairIdx X k)) z :=
    cellPair_of_eq (by omega) z
  unfold injectPair
  rw [hid, ← Finsupp.mapDomain_comp, hcell]
  rfl

/-- **The published diagonal, bidegree by bidegree.**  Every later computation
runs on this form. -/
theorem phiPair_eq (X : TopCat.{0}) (k : ℕ) (n : Fin (k + 1))
    (σ : singularSimplices X n.val) :
    phiPair X k ⟨n, σ⟩ = ∑ a ∈ Finset.range (k + 1), phiCell X k (k - n.val) a (k - a) σ := by
  have hb : phiBasis X (ZMod 2) (⟨n, σ⟩ : WSIndex X k)
      = ∑ a : Fin (k + 1),
          injectPair X (ZMod 2) a (steenrodDiag (k - n.val) a.val (k - a.val) σ) := rfl
  have hterm : ∀ a : Fin (k + 1),
      Finsupp.mapDomain (pairIndexToIdx X k)
          (injectPair X (ZMod 2) a (steenrodDiag (k - n.val) a.val (k - a.val) σ))
        = phiCell X k (k - n.val) a.val (k - a.val) σ :=
    fun a => mapDomain_injectPair X a _
  unfold phiPair
  rw [hb, mapDomain_finset_sum,
    Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => hterm a)]
  exact Fin.sum_univ_eq_sum_range (fun a => phiCell X k (k - n.val) a (k - a) σ) (k + 1)

/-! ## 3. The two halves of the target differential -/

/-- `∂ ⊗ 1` on the whole degree-`k+1` module. -/
def dTgtL (X : TopCat.{0}) (k : ℕ) :
    (PairIdx X (k + 1) →₀ ZMod 2) →ₗ[ZMod 2] (PairIdx X k →₀ ZMod 2) :=
  Finsupp.linearCombination (ZMod 2)
    (fun q : PairIdx X (k + 1) =>
      dLeft X (ZMod 2) k q.1.val.1 q.1.val.2 q.1.property q.2.1 q.2.2)

/-- `1 ⊗ ∂` on the whole degree-`k+1` module. -/
def dTgtR (X : TopCat.{0}) (k : ℕ) :
    (PairIdx X (k + 1) →₀ ZMod 2) →ₗ[ZMod 2] (PairIdx X k →₀ ZMod 2) :=
  Finsupp.linearCombination (ZMod 2)
    (fun q : PairIdx X (k + 1) =>
      dRight X (ZMod 2) k q.1.val.1 q.1.val.2 q.1.property q.2.1 q.2.2)

theorem dTgtL_single (k : ℕ) (q : PairIdx X (k + 1)) (c : ZMod 2) :
    dTgtL X k (Finsupp.single q c)
      = c • dLeft X (ZMod 2) k q.1.val.1 q.1.val.2 q.1.property q.2.1 q.2.2 := by
  unfold dTgtL
  simp

theorem dTgtR_single (k : ℕ) (q : PairIdx X (k + 1)) (c : ZMod 2) :
    dTgtR X k (Finsupp.single q c)
      = c • dRight X (ZMod 2) k q.1.val.1 q.1.val.2 q.1.property q.2.1 q.2.2 := by
  unfold dTgtR
  simp

/-- **The target differential is the sum of its two halves**, as operators. -/
theorem dTgt_eq_add (k : ℕ) (y : PairIdx X (k + 1) →₀ ZMod 2) :
    dTgt X (ZMod 2) k y = dTgtL X k y + dTgtR X k y := by
  classical
  refine Finsupp.induction_linear y ?_ ?_ ?_
  · simp
  · intro u v hu hv
    rw [map_add, map_add, map_add, hu, hv]
    abel
  · intro q c
    rw [dTgt_single, dTgtL_single, dTgtR_single, dGen_eq]
    exact smul_add c _ _

/-! ## 4. Each half of the differential, on one bidegree -/

theorem dTgtL_cellPair_single (k a b : ℕ)
    (p : singularSimplices X (a + 1) × singularSimplices X b) :
    dTgtL X k (cellPair X (k + 1) (a + 1) b (Finsupp.single p 1))
      = cellPair X k a b (tenBdL X a b (Finsupp.single p 1)) := by
  rw [cellPair_single_one]
  by_cases h : a + 1 + b = k + 1
  · have ha : a + b = k := by omega
    rw [padIdx_of_eq h, dTgtL_single, one_smul]
    show dLeft X (ZMod 2) k (a + 1) b h p.1 p.2
        = cellPair X k a b (tenBdL X a b (Finsupp.single p 1))
    rw [dLeft_succ, tenBdL_single, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [cellPair_single_one]
    exact (padIdx_of_eq ha (faceSimplex X a j p.1, p.2)).symm
  · have ha : ¬ a + b = k := by omega
    rw [padIdx_of_ne h, map_zero, cellPair_of_ne ha]

theorem dTgtR_cellPair_single (k a b : ℕ)
    (p : singularSimplices X a × singularSimplices X (b + 1)) :
    dTgtR X k (cellPair X (k + 1) a (b + 1) (Finsupp.single p 1))
      = cellPair X k a b (tenBdR X a b (Finsupp.single p 1)) := by
  rw [cellPair_single_one]
  by_cases h : a + (b + 1) = k + 1
  · have ha : a + b = k := by omega
    rw [padIdx_of_eq h, dTgtR_single, one_smul]
    show dRight X (ZMod 2) k a (b + 1) h p.1 p.2
        = cellPair X k a b (tenBdR X a b (Finsupp.single p 1))
    rw [dRight_succ, tenBdR_single, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [cellPair_single_one]
    exact (padIdx_of_eq ha (p.1, faceSimplex X b j p.2)).symm
  · have ha : ¬ a + b = k := by omega
    rw [padIdx_of_ne h, map_zero, cellPair_of_ne ha]

theorem dTgtL_cellPair (k a b : ℕ) (z : tensorTwo X (a + 1) b) :
    dTgtL X k (cellPair X (k + 1) (a + 1) b z) = cellPair X k a b (tenBdL X a b z) := by
  classical
  refine Finsupp.induction_linear z ?_ ?_ ?_
  · simp
  · intro u v hu hv
    rw [map_add, map_add, hu, hv, map_add, map_add]
  · intro p c
    have hs : (Finsupp.single p c : tensorTwo X (a + 1) b)
        = c • Finsupp.single p (1 : ZMod 2) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hs, map_smul, map_smul, map_smul, map_smul]
    exact congrArg (fun w => c • w) (dTgtL_cellPair_single k a b p)

theorem dTgtR_cellPair (k a b : ℕ) (z : tensorTwo X a (b + 1)) :
    dTgtR X k (cellPair X (k + 1) a (b + 1) z) = cellPair X k a b (tenBdR X a b z) := by
  classical
  refine Finsupp.induction_linear z ?_ ?_ ?_
  · simp
  · intro u v hu hv
    rw [map_add, map_add, hu, hv, map_add, map_add]
  · intro p c
    have hs : (Finsupp.single p c : tensorTwo X a (b + 1))
        = c • Finsupp.single p (1 : ZMod 2) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hs, map_smul, map_smul, map_smul, map_smul]
    exact congrArg (fun w => c • w) (dTgtR_cellPair_single k a b p)

/-- In left degree `0` the first factor has no boundary. -/
theorem dTgtL_cellPair_zero (k b : ℕ) (z : tensorTwo X 0 b) :
    dTgtL X k (cellPair X (k + 1) 0 b z) = 0 := by
  classical
  refine Finsupp.induction_linear z ?_ ?_ ?_
  · simp
  · intro u v hu hv
    rw [map_add, map_add, hu, hv]
    exact add_zero _
  · intro p c
    rw [cellPair_single, map_smul]
    by_cases h : 0 + b = k + 1
    · rw [padIdx_of_eq h, dTgtL_single, one_smul]
      show c • dLeft X (ZMod 2) k 0 b h p.1 p.2 = 0
      rw [dLeft_zero]
      exact smul_zero c
    · rw [padIdx_of_ne h, map_zero]
      exact smul_zero c

/-- In right degree `0` the second factor has no boundary. -/
theorem dTgtR_cellPair_zero (k a : ℕ) (z : tensorTwo X a 0) :
    dTgtR X k (cellPair X (k + 1) a 0 z) = 0 := by
  classical
  refine Finsupp.induction_linear z ?_ ?_ ?_
  · simp
  · intro u v hu hv
    rw [map_add, map_add, hu, hv]
    exact add_zero _
  · intro p c
    rw [cellPair_single, map_smul]
    by_cases h : a + 0 = k + 1
    · rw [padIdx_of_eq h, dTgtR_single, one_smul]
      show c • dRight X (ZMod 2) k a 0 h p.1 p.2 = 0
      rw [dRight_zero]
      exact smul_zero c
    · rw [padIdx_of_ne h, map_zero]
      exact smul_zero c

/-! ## 5. The swap, bidegree by bidegree -/

theorem swapEnd_cellPair (k a b : ℕ) (z : tensorTwo X a b) :
    swapEnd X k (cellPair X k a b z) = cellPair X k b a (tensorSwap a b z) := by
  by_cases h : a + b = k
  · have hb : b + a = k := by omega
    have hL : swapEnd X k (cellPair X k a b z)
        = Finsupp.mapDomain
            (swapIdx ∘ (fun p => (⟨⟨(a, b), h⟩, p⟩ : PairIdx X k))) z := by
      rw [cellPair_of_eq h]
      unfold swapEnd
      rw [Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
    have hR : cellPair X k b a (tensorSwap a b z)
        = Finsupp.mapDomain
            ((fun p => (⟨⟨(b, a), hb⟩, p⟩ : PairIdx X k)) ∘ Prod.swap) z := by
      rw [cellPair_of_eq hb]
      unfold tensorSwap
      rw [← Finsupp.mapDomain_comp]
    rw [hL, hR]
    rfl
  · have hb : ¬ b + a = k := by omega
    rw [cellPair_of_ne h, cellPair_of_ne hb]
    exact map_zero _

/-- One bidegree of `T Φ(e_i ⊗ σ)`. -/
def phiCellSwap (X : TopCat.{0}) (k i a b : ℕ) {N : ℕ} (σ : singularSimplices X N) :
    PairIdx X k →₀ ZMod 2 :=
  cellPair X k a b (tensorSwap b a (steenrodDiag i b a σ))

theorem phiCellSwap_congr_b (k i a : ℕ) {b b' N : ℕ} (σ : singularSimplices X N)
    (h : b = b') : phiCellSwap X k i a b σ = phiCellSwap X k i a b' σ := by
  subst h
  rfl

/-- **The equivariance step.**  The geometric swap on the degree-`k` module
reverses the bidegree, `a ↦ k - a`, and swaps the two factors inside it.  The
reversal is an involution of `Finset.range (k+1)`, which is the only thing
`k - (k - a) = a` is needed for, and it is needed on plain naturals. -/
theorem swapEnd_phiSum (k i : ℕ) {N : ℕ} (σ : singularSimplices X N) :
    swapEnd X k (∑ a ∈ Finset.range (k + 1), phiCell X k i a (k - a) σ)
      = ∑ a ∈ Finset.range (k + 1), phiCellSwap X k i a (k - a) σ := by
  rw [map_sum]
  have hterm : ∀ a ∈ Finset.range (k + 1),
      swapEnd X k (phiCell X k i a (k - a) σ) = phiCellSwap X k i (k - a) a σ :=
    fun a _ => swapEnd_cellPair k a (k - a) (steenrodDiag i a (k - a) σ)
  rw [Finset.sum_congr rfl hterm]
  refine Finset.sum_nbij' (fun a => k - a) (fun a => k - a) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_range] at ha ⊢
    omega
  · intro a ha
    rw [Finset.mem_range] at ha ⊢
    omega
  · intro a ha
    rw [Finset.mem_range] at ha
    omega
  · intro a ha
    rw [Finset.mem_range] at ha
    omega
  · intro a ha
    rw [Finset.mem_range] at ha
    exact phiCellSwap_congr_b k i (k - a) σ (by omega)

/-! ## 6. Characteristic two -/

theorem pair_add_self {α : Type*} (y : α →₀ ZMod 2) : y + y = 0 := by
  ext p
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  rw [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply]
  exact h2 _

end

end Steenrod
end CharClass
end GroupApproximation
