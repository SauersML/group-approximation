import GroupApproximation.CharClass.CartanEvalPre
import GroupApproximation.CharClass.SteenrodFourfoldBTransport

/-!
# Evaluating the second composite

Composite B, paired against `α, β, α, β`, is the sum over the splittings of the
resolution index of the cup product of the two cup-`i` squares.  That is the
right-hand side of the Cartan formula.

Three things do the work.  The interchange turns the functional into the one
that gives each cochain both factors of one diagonal value.  The power of the
generator on the second block is invisible, because that pairing has equal
cochains.  And the pairing against the diagonal is the cup-`i` product, so each
block contributes a square and the outer pairing against `Φ₀` multiplies them.

No degree hypothesis survives.  The cup-`i` product of two cochains of the wrong
degrees is zero, which is the same condition as the pairing's bidegree selection,
so writing the squares at the degrees they actually have makes every off-diagonal
term vanish on both sides at once.

## Main results

* `fourEvalPre_compBPre` — one term, evaluated.
* `fourEvalF2_compBGen` — **composite B evaluated**.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

variable {X : TopCat.{0}}

/-- Evaluating a cup-`i` product at the degree it actually has.  Both sides
vanish off that degree, and for the same reason. -/
theorem cochainEval_cochainCupI_eq_evAt (j a b : ℕ)
    (γ : singularCochainGroup (ZMod 2) X a) (δ : singularCochainGroup (ZMod 2) X b)
    {N : ℕ} (τ : singularSimplices X N) :
    cochainEval N (cochainCupI j a b N γ δ) τ
      = evAt X (a + b - j) (cochainCupI j a b (a + b - j) γ δ) N τ := by
  by_cases h : N = a + b - j
  · subst h
    rw [evAt_self]
  · rw [evAt_of_ne X (a + b - j) _ N h]
    by_cases h2 : a + b = N + j
    · exact absurd (show N = a + b - j by omega) h
    · rw [cochainCupI_of_degree_ne j a b N h2, cochainEval_zero]

/-- **One term of composite B, evaluated.**  The two blocks contribute the two
cup-`i` squares. -/
theorem fourEvalPre_compBPre (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (i j N : ℕ) (hj : j ≤ i) (r : Steenrod.PairIdx X N) :
    fourEvalPre X p q α β (N + i) (Steenrod.compBPre X (N + i) i j N r)
      = pairEvalGen X (p + p - j) (q + q - (i - j))
          (cochainCupI j p p (p + p - j) α α)
          (cochainCupI (i - j) q q (q + q - (i - j)) β β) N r := by
  have hdeg : r.1.val.1 + r.1.val.2 = N := r.1.property
  have hsum : r.1.val.1 + j + (r.1.val.2 + (i - j)) = N + i := by omega
  show fourEvalPre X p q α β (N + i)
      (Steenrod.padFour X (N + i) (r.1.val.1 + j) (r.1.val.2 + (i - j))
        (Steenrod.phiAtDeg X (r.1.val.1 + j) j r.2.1)
        ((groupRingGen ^ j : GroupRingZ2) •
          Steenrod.phiAtDeg X (r.1.val.2 + (i - j)) (i - j) r.2.2)) = _
  rw [fourEvalPre_padFour_of_eq X p q α β (N + i) (r.1.val.1 + j) (r.1.val.2 + (i - j))
      hsum, pairEvalIdx_pow_smul, pairEvalIdx_phiAtDeg_eq, pairEvalIdx_phiAtDeg_eq]
  show cochainEval r.1.val.1 (cochainCupI j p p r.1.val.1 α α) r.2.1
      * cochainEval r.1.val.2 (cochainCupI (i - j) q q r.1.val.2 β β) r.2.2 = _
  rw [cochainEval_cochainCupI_eq_evAt j p p α α r.2.1,
    cochainEval_cochainCupI_eq_evAt (i - j) q q β β r.2.2]
  rfl

/-- One summand of composite B, over the whole of `Φ₀(σ)`. -/
theorem fourEvalPre_linearCombination (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (i j N : ℕ) (hj : j ≤ i) (z : Steenrod.PairIdx X N →₀ ZMod 2) :
    fourEvalPre X p q α β (N + i)
        (Finsupp.linearCombination (ZMod 2) (Steenrod.compBPre X (N + i) i j N) z)
      = pairEvalIdx X (p + p - j) (q + q - (i - j))
          (cochainCupI j p p (p + p - j) α α)
          (cochainCupI (i - j) q q (q + q - (i - j)) β β) N z := by
  induction z using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero]
  | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]
  | single r c =>
      rw [Finsupp.linearCombination_single, map_smul, smul_eq_mul, pairEvalIdx_single,
        fourEvalPre_compBPre p q α β i j N hj r]

/-- **Composite B evaluated**: the right-hand side of the Cartan formula, at
cochain level. -/
theorem fourEvalF2_compBGen (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (i : ℕ) {N : ℕ} (σ : singularSimplices X N) :
    fourEvalF2 X p q α β (N + i) (Steenrod.compBGen X (N + i) i σ)
      = ∑ j ∈ Finset.range (i + 1),
          evAt X (p + p - j + (q + q - (i - j)))
            (cochainCup (p + p - j) (q + q - (i - j))
              (cochainCupI j p p (p + p - j) α α)
              (cochainCupI (i - j) q q (q + q - (i - j)) β β)) N σ := by
  rw [Steenrod.compBGen_eq_midSwap, fourEvalF2_midSwap]
  show fourEvalPre X p q α β (N + i)
      (∑ j ∈ Finset.range (i + 1),
        Finsupp.linearCombination (ZMod 2) (Steenrod.compBPre X (N + i) i j N)
          (Steenrod.phiZero X N σ)) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [fourEvalPre_linearCombination p q α β i j N
      (by have := Finset.mem_range.mp hj; omega) (Steenrod.phiZero X N σ),
    pairEvalIdx_phiZero_eq_evAt]

end

end GroupApproximation.CharClass
