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

theorem compBTerm_eq (X : TopCat.{0}) (k i p N : ℕ) (r : PairIdx X N) :
    compBTerm X k i p N r
      = padFour X k (r.1.val.1 + p) (r.1.val.2 + (i - p))
          (phiAtDeg X (r.1.val.1 + p) p r.2.1)
          ((groupRingGen ^ p) • phiAtDeg X (r.1.val.2 + (i - p)) (i - p) r.2.2) := rfl

/-- **The Leibniz rule on one term** of the double sum defining `B`. -/
theorem tensorD_compBTerm (X : TopCat.{0}) (k i p N : ℕ) (r : PairIdx X N) :
    tensorD (pairFreeCx X) (pairFreeCx X) k (compBTerm X (k + 1) i p N r)
      = padFourL X k (r.1.val.1 + p) (r.1.val.2 + (i - p))
            (phiAtDeg X (r.1.val.1 + p) p r.2.1)
            ((groupRingGen ^ p) • phiAtDeg X (r.1.val.2 + (i - p)) (i - p) r.2.2)
        + padFourR X k (r.1.val.1 + p) (r.1.val.2 + (i - p))
            (phiAtDeg X (r.1.val.1 + p) p r.2.1)
            ((groupRingGen ^ p) • phiAtDeg X (r.1.val.2 + (i - p)) (i - p) r.2.2) := by
  rw [compBTerm_eq, tensorD_padFour]

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

end

end Steenrod
end CharClass
end GroupApproximation
