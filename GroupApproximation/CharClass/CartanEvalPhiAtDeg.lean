import GroupApproximation.CharClass.CartanEvalAW
import GroupApproximation.CharClass.SteenrodFourfoldBDecomp

/-!
# Pairing two cochains against the diagonal at a free cut index

`pairEvalIdx_phiPair` did this for the diagonal as it appears in the source
complex, where the cut index is determined by the `W`-index.  Composite B needs
it with the cut index free, because the resolution's diagonal splits it into two
independent halves.

The statement needs no degree hypothesis once the pair degree is written as
`N + j`, the degree the diagonal actually lands in: off the cochains' own
bidegree the left side vanishes by bidegree selection and the right side vanishes
because the cup-`i` product of two cochains of the wrong degrees is zero, and
those are the same condition.

## Main results

* `pairEvalIdx_phiAtDeg_eq` — **the pairing against the diagonal at cut index
  `j`** is the evaluation of the cup-`j` product.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

variable {X : TopCat.{0}}

theorem pairEvalIdx_phiAtDeg (p q m j : ℕ) (h : p + q = m)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    {N : ℕ} (σ : singularSimplices X N) :
    pairEvalIdx X p q α β m (Steenrod.phiAtDeg X m j σ)
      = cochainEval N (cochainCupI j p q N α β) σ := by
  show pairEvalIdx X p q α β m
    (∑ a ∈ Finset.range (m + 1), Steenrod.phiCell X m j a (m - a) σ) = _
  rw [map_sum]
  refine (Finset.sum_eq_single p ?_ ?_).trans ?_
  · intro a _ hne
    show pairEvalIdx X p q α β m
      (Steenrod.cellPair X m a (m - a) (steenrodDiag j a (m - a) σ)) = 0
    exact pairEvalIdx_cellPair_of_ne_left p q m a (m - a) hne α β _
  · intro hp
    exact absurd (Finset.mem_range.mpr (show p < m + 1 by omega)) hp
  · rw [Steenrod.phiCell_congr_b (X := X) m j p σ (show m - p = q by omega)]
    exact pairEvalIdx_phiCell_self m j p q h α β σ

theorem pairEvalIdx_phiAtDeg_of_ne (p q m j : ℕ) (h : ¬ p + q = m)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    {N : ℕ} (σ : singularSimplices X N) :
    pairEvalIdx X p q α β m (Steenrod.phiAtDeg X m j σ) = 0 := by
  show pairEvalIdx X p q α β m
    (∑ a ∈ Finset.range (m + 1), Steenrod.phiCell X m j a (m - a) σ) = 0
  rw [map_sum]
  refine Finset.sum_eq_zero fun a ha => ?_
  show pairEvalIdx X p q α β m
    (Steenrod.cellPair X m a (m - a) (steenrodDiag j a (m - a) σ)) = 0
  by_cases hap : a = p
  · refine pairEvalIdx_cellPair_of_ne_right p q m a (m - a) ?_ α β _
    have hle : a ≤ m := by
      have hm := Finset.mem_range.mp ha
      omega
    omega
  · exact pairEvalIdx_cellPair_of_ne_left p q m a (m - a) hap α β _

/-- **The pairing against the diagonal at cut index `j`.**  No degree hypothesis:
off the cochains' own bidegree both sides vanish, and for the same reason. -/
theorem pairEvalIdx_phiAtDeg_eq (p q j : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    {N : ℕ} (σ : singularSimplices X N) :
    pairEvalIdx X p q α β (N + j) (Steenrod.phiAtDeg X (N + j) j σ)
      = cochainEval N (cochainCupI j p q N α β) σ := by
  by_cases h : p + q = N + j
  · exact pairEvalIdx_phiAtDeg p q (N + j) j h α β σ
  · rw [pairEvalIdx_phiAtDeg_of_ne p q (N + j) j h α β σ,
      cochainCupI_of_degree_ne j p q N h α β, cochainEval_zero]

end

end GroupApproximation.CharClass
