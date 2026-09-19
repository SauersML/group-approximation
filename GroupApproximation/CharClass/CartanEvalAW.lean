import GroupApproximation.CharClass.CartanEvalPair
import GroupApproximation.CharClass.CartanEvalFour
import GroupApproximation.CharClass.SteenrodFourfoldAW
import GroupApproximation.CharClass.SteenrodCupEdge

/-!
# The fourfold functional factors through the pair functional

Evaluating four cochains on the fourfold is evaluating two of them on each pair
factor.  That is true on the nose, because the functional on a basis element of
the fourfold *is* the product of the two pair values: `fourEvalGen_eq` is `rfl`.

On top of that, the Alexander–Whitney diagonal turns the pair functional into the
cup product: pairing `α` and `β` against `Φ₀(σ)` is evaluating `α ⌣ β` on `σ`,
and it vanishes unless `σ` has degree `p + q`, which is exactly what `evAt` says.

## Main results

* `fourEvalGen_eq`, `fourEvalF2_tenElt_pair` — the factorisation.
* `pairEvalIdx_phiZero_eq_evAt` — **the cup product**: pairing two cochains
  against the Alexander–Whitney diagonal is evaluating their cup product, in
  every degree at once.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

variable {X : TopCat.{0}} (p q : ℕ)
  (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)

/-! ## 1. The fourfold functional is the product of the two pair functionals -/

/-- On a basis element, the fourfold functional is the product of the two pair
functionals.  Both sides are the same four factors, associated the same way. -/
theorem fourEvalGen_eq {k : ℕ} (Z : TensorIdx (pairFreeCx X) (pairFreeCx X) k) :
    fourEvalGen X p q α β Z
      = pairEvalGen X p q α β Z.1.val.1 Z.2.1 * pairEvalGen X p q α β Z.1.val.2 Z.2.2 :=
  rfl

theorem fourEvalF2_tenElt_single_single (k a b : ℕ) (h : a + b = k)
    (u : Steenrod.PairIdx X a) (v : Steenrod.PairIdx X b) :
    fourEvalF2 X p q α β k
        (tenElt (pairFreeCx X) (pairFreeCx X) (⟨(a, b), h⟩ : Steenrod.PairDeg k)
          (Finsupp.single u 1) (Finsupp.single v 1))
      = pairEvalGen X p q α β a u * pairEvalGen X p q α β b v := by
  rw [tenElt_single_single, fourEvalF2_single, one_mul]
  rfl

/-- **The factorisation.** -/
theorem fourEvalF2_tenElt_pair (k a b : ℕ) (h : a + b = k)
    (U : Steenrod.PairIdx X a →₀ ZMod 2) (V : Steenrod.PairIdx X b →₀ ZMod 2) :
    fourEvalF2 X p q α β k
        (tenElt (pairFreeCx X) (pairFreeCx X) (⟨(a, b), h⟩ : Steenrod.PairDeg k) U V)
      = pairEvalIdx X p q α β a U * pairEvalIdx X p q α β b V := by
  induction U using Finsupp.induction_linear with
  | zero => rw [tenElt_zero_left, map_zero, map_zero, zero_mul]
  | add u1 u2 h1 h2 => rw [tenElt_add_left, map_add, h1, h2, map_add, add_mul]
  | single u c =>
      induction V using Finsupp.induction_linear with
      | zero => rw [tenElt_zero_right, map_zero, map_zero, mul_zero]
      | add v1 v2 g1 g2 => rw [tenElt_add_right, map_add, g1, g2, map_add, mul_add]
      | single v d =>
          rw [pairEvalIdx_single, pairEvalIdx_single,
            show (Finsupp.single u c : Steenrod.PairIdx X a →₀ ZMod 2)
                = c • Finsupp.single u (1 : ZMod 2) by
              rw [Finsupp.smul_single, smul_eq_mul, mul_one],
            show (Finsupp.single v d : Steenrod.PairIdx X b →₀ ZMod 2)
                = d • Finsupp.single v (1 : ZMod 2) by
              rw [Finsupp.smul_single, smul_eq_mul, mul_one],
            tenElt_smul_left, tenElt_smul_right, map_smul, map_smul, smul_eq_mul,
            smul_eq_mul, fourEvalF2_tenElt_single_single]
          ring

/-! ## 2. The Alexander–Whitney diagonal is the cup product -/

/-- On the matching total degree, pairing against `Φ₀` is the cup-`0` product. -/
theorem pairEvalIdx_phiZero (n : ℕ) (h : p + q = n) (σ : singularSimplices X n) :
    pairEvalIdx X p q α β n (Steenrod.phiZero X n σ)
      = cochainEval n (cochainCupI 0 p q n α β) σ := by
  show pairEvalIdx X p q α β n
    (∑ a ∈ Finset.range (n + 1), Steenrod.phiCell X n 0 a (n - a) σ) = _
  rw [map_sum]
  refine (Finset.sum_eq_single p ?_ ?_).trans ?_
  · intro a _ hne
    show pairEvalIdx X p q α β n
      (Steenrod.cellPair X n a (n - a) (steenrodDiag 0 a (n - a) σ)) = 0
    exact pairEvalIdx_cellPair_of_ne_left p q n a (n - a) hne α β _
  · intro hp
    exact absurd (Finset.mem_range.mpr (show p < n + 1 by omega)) hp
  · rw [Steenrod.phiCell_congr_b (X := X) n 0 p σ (show n - p = q by omega)]
    exact pairEvalIdx_phiCell_self n 0 p q h α β σ

/-- Off the matching total degree the pairing vanishes: every bidegree of `Φ₀`
has the wrong first factor or the wrong second one. -/
theorem pairEvalIdx_phiZero_of_ne (n : ℕ) (h : p + q ≠ n) (σ : singularSimplices X n) :
    pairEvalIdx X p q α β n (Steenrod.phiZero X n σ) = 0 := by
  show pairEvalIdx X p q α β n
    (∑ a ∈ Finset.range (n + 1), Steenrod.phiCell X n 0 a (n - a) σ) = 0
  rw [map_sum]
  refine Finset.sum_eq_zero fun a ha => ?_
  show pairEvalIdx X p q α β n
    (Steenrod.cellPair X n a (n - a) (steenrodDiag 0 a (n - a) σ)) = 0
  by_cases hap : a = p
  · refine pairEvalIdx_cellPair_of_ne_right p q n a (n - a) ?_ α β _
    have : a ≤ n := by
      have := Finset.mem_range.mp ha
      omega
    omega
  · exact pairEvalIdx_cellPair_of_ne_left p q n a (n - a) hap α β _

/-- **Pairing two cochains against the Alexander–Whitney diagonal is evaluating
their cup product**, in every degree at once: both sides vanish off degree
`p + q`, and for the same reason. -/
theorem pairEvalIdx_phiZero_eq_evAt (n : ℕ) (σ : singularSimplices X n) :
    pairEvalIdx X p q α β n (Steenrod.phiZero X n σ)
      = evAt X (p + q) (cochainCup p q α β) n σ := by
  by_cases h : p + q = n
  · subst h
    rw [pairEvalIdx_phiZero p q α β (p + q) rfl σ, cochainCupI_zero, evAt_self]
  · rw [pairEvalIdx_phiZero_of_ne p q α β n h σ,
      evAt_of_ne X (p + q) (cochainCup p q α β) n (fun hn => h hn.symm) σ]

end

end GroupApproximation.CharClass
