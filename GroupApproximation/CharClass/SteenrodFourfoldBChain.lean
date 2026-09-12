import GroupApproximation.CharClass.SteenrodFourfoldBridge
import GroupApproximation.CharClass.SteenrodFourfoldAW

/-!
# The chain-map computation for `B`, first layer

The chain-map property of the second composite is the one genuine computation in
this lane's share of the Cartan comparison.  This file carries the differential
inside the double sum that defines `B`, which is the step everything else is
stated on top of.

Two facts make the rest of the computation possible and are proved here.

**The diagonal vanishes above the dimension.**  `Φ(e_j ⊗ σ')` is zero whenever
`j` exceeds the degree of `σ'`, because there are no `(j+1)`-element sets of cut
points in a smaller simplex.  That is what kills the terms of the double sum in
which the front face is too small to carry its share of the resolution index, and
it is why the four term families of the computation have as few edge cases as
they do.

**The differential passes through a linear combination.**  `B` is a sum over the
resolution index of a linear combination over the basis of `Φ₀(σ)`, so
differentiating it is differentiating each basis value.

## Main results

* `phiAtDeg_eq_zero_of_lt` — the diagonal above the dimension.
* `tensorD_compBTerm` — the Leibniz rule on one term of the double sum.
* `tensorD_compBGen` — the differential, carried inside the double sum.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-! ## 1. The diagonal above the dimension -/

/-- `Φ(e_i ⊗ σ)` vanishes once `i` exceeds the dimension of `σ`: an `N`-simplex
has no `(i+1)`-element set of cut points when `i > N`. -/
theorem phiAtDeg_eq_zero_of_lt (X : TopCat.{0}) (m i N : ℕ)
    (σ : singularSimplices X N) (h : N < i) : phiAtDeg X m i σ = 0 := by
  unfold phiAtDeg
  refine Finset.sum_eq_zero fun a _ => ?_
  unfold phiCell
  rw [steenrodDiag_eq_zero_of_lt i a (m - a) σ h]
  exact map_zero (cellPair X m a (m - a))

/-! ## 2. A linear map through a linear combination -/

theorem apply_linearCombination' {α M N : Type} [AddCommGroup M] [Module (ZMod 2) M]
    [AddCommGroup N] [Module (ZMod 2) N] (L : M →ₗ[ZMod 2] N) (g : α → M)
    (z : α →₀ ZMod 2) :
    L (Finsupp.linearCombination (ZMod 2) g z)
      = Finsupp.linearCombination (ZMod 2) (fun a => L (g a)) z := by
  classical
  induction z using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero]
  | add u v hu hv => rw [map_add, map_add, hu, hv, map_add]
  | single a c =>
      have h1 : Finsupp.linearCombination (ZMod 2) g (Finsupp.single a c) = c • g a := by
        simp
      have h2 : Finsupp.linearCombination (ZMod 2) (fun a => L (g a))
          (Finsupp.single a c) = c • L (g a) := by
        simp
      rw [h1, h2, map_smul]

/-! ## 3. The differential, carried inside the double sum -/

theorem compBPre_eq (X : TopCat.{0}) (k i p N : ℕ) (r : PairIdx X N) :
    compBPre X k i p N r
      = padFour X k (r.1.val.1 + p) (r.1.val.2 + (i - p))
          (phiAtDeg X (r.1.val.1 + p) p r.2.1)
          ((groupRingGen ^ p) • phiAtDeg X (r.1.val.2 + (i - p)) (i - p) r.2.2) := rfl

/-- **The Leibniz rule on one term** of the double sum defining `B`, before the
middle interchange.  Pushing the differential through the interchange itself is
`cc-cartan`'s `midSwap` chain-map property. -/
theorem tensorD_compBPre (X : TopCat.{0}) (k i p N : ℕ) (r : PairIdx X N) :
    tensorD (pairFreeCx X) (pairFreeCx X) k (compBPre X (k + 1) i p N r)
      = padFourL X k (r.1.val.1 + p) (r.1.val.2 + (i - p))
            (phiAtDeg X (r.1.val.1 + p) p r.2.1)
            ((groupRingGen ^ p) • phiAtDeg X (r.1.val.2 + (i - p)) (i - p) r.2.2)
        + padFourR X k (r.1.val.1 + p) (r.1.val.2 + (i - p))
            (phiAtDeg X (r.1.val.1 + p) p r.2.1)
            ((groupRingGen ^ p) • phiAtDeg X (r.1.val.2 + (i - p)) (i - p) r.2.2) := by
  rw [compBPre_eq, tensorD_padFour]

/-- **The differential of `B`, carried inside the double sum.**  Everything the
rest of the computation says is a statement about the summand. -/
theorem tensorD_compBGen (X : TopCat.{0}) (k i N : ℕ) (σ : singularSimplices X N) :
    tensorD (pairFreeCx X) (pairFreeCx X) k (compBGen X (k + 1) i σ)
      = ∑ p ∈ Finset.range (i + 1),
          Finsupp.linearCombination (ZMod 2)
            (fun r : PairIdx X N =>
              tensorD (pairFreeCx X) (pairFreeCx X) k (compBTerm X (k + 1) i p N r))
            (phiZero X N σ) := by
  unfold compBGen
  rw [map_sum]
  exact Finset.sum_congr rfl fun p _ =>
    apply_linearCombination' (tensorD (pairFreeCx X) (pairFreeCx X) k)
      (compBTerm X (k + 1) i p N) (phiZero X N σ)

/-! ## 4. Which terms of the double sum survive

Two vanishing lemmas cut the case analysis of the computation in half.  A block
of the Leibniz rule is zero as soon as the factor it differentiates is zero, and
the factor is zero as soon as the resolution index exceeds the dimension of the
face it is applied to.  So in the left block only the terms whose front face is
at least as big as its share of the index survive, and dually on the right. -/

theorem padFourL_of_zero_left (X : TopCat.{0}) (k a b : ℕ)
    (v : PairIdx X b →₀ ZMod 2) :
    padFourL X k a b 0 v = 0 := by
  cases a with
  | zero => exact padFourL_zero_deg X k b 0 v
  | succ a' =>
      rw [padFourL_succ_eq', map_zero]
      exact padFour_zero_left k a' b v

theorem padFourR_of_zero_right (X : TopCat.{0}) (k a b : ℕ)
    (u : PairIdx X a →₀ ZMod 2) :
    padFourR X k a b u 0 = 0 := by
  cases b with
  | zero => exact padFourR_zero_deg X k a u 0
  | succ b' =>
      rw [padFourR_succ_eq', map_zero]
      exact padFour_zero_right k a b' u

/-- **The left block dies when the front face is too small** to carry its share
of the resolution index. -/
theorem padFourL_term_eq_zero (X : TopCat.{0}) (k c p b : ℕ)
    (σ' : singularSimplices X c) (v : PairIdx X b →₀ ZMod 2) (hc : c < p) :
    padFourL X k (c + p) b (phiAtDeg X (c + p) p σ') v = 0 := by
  rw [phiAtDeg_eq_zero_of_lt X (c + p) p c σ' hc]
  exact padFourL_of_zero_left X k (c + p) b v

/-- **The right block dies when the back face is too small.**  The power of the
generator does not save it: the group ring acts by a linear involution, so it
sends `0` to `0`. -/
theorem padFourR_term_eq_zero (X : TopCat.{0}) (k a d p q : ℕ)
    (u : PairIdx X a →₀ ZMod 2) (σ'' : singularSimplices X d) (hd : d < q) :
    padFourR X k a (d + q) u ((groupRingGen ^ p) • phiAtDeg X (d + q) q σ'') = 0 := by
  rw [phiAtDeg_eq_zero_of_lt X (d + q) q d σ'' hd, smul_zero]
  exact padFourR_of_zero_right X k a (d + q) u

end

end Steenrod
end CharClass
end GroupApproximation
