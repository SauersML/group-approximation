import GroupApproximation.CharClass.SteenrodFourfoldBFree

/-!
# Every branch of the summand identity

With all four degrees of the summand free, each branch of the Leibniz expansion
is a single rewrite chain: the block lemma at a successor degree, then the
boundary identity for `Φ` at the index that block differentiates.  No arithmetic
is reconciled anywhere, which is the point of the free-degree form.

The branches are: the block vanishes when its own degree is zero; it vanishes
when the face it differentiates is too small to carry its index; and otherwise it
splits, with a `(1 + T)` part exactly when that index is a successor.

## Main results

* `bTerm_left_succ_succ`, `bTerm_left_succ_zero` — the two live left branches.
* `bTerm_right_succ_succ`, `bTerm_right_succ_zero` — the two live right branches.
* `bTerm_left_small`, `bTerm_right_small` — the vanishing branches.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-- **Left block, index a successor.**  The `(1 + T)` part and the face part. -/
theorem bTerm_left_succ_succ (X : TopCat.{0}) (k a' b p' q M' : ℕ) {d : ℕ}
    (ρ : singularSimplices X (M' + 1)) (τ : singularSimplices X d) :
    padFourL X k (a' + 1) b (phiAtDeg X (a' + 1) (p' + 1) ρ)
        ((groupRingGen ^ (p' + 1)) • phiAtDeg X b q τ)
      = padFour X k a' b
          ((phiAtDeg X a' p' ρ + swapEnd X a' (phiAtDeg X a' p' ρ))
            + ∑ jj : Fin (M' + 2), phiAtDeg X a' (p' + 1) (faceSimplex X M' jj ρ))
          ((groupRingGen ^ (p' + 1)) • phiAtDeg X b q τ) := by
  rw [padFourL_bTerm_succ, dTgt_phiAtDeg_succ X a' p' M' ρ]

/-- **Left block, index zero.**  The face part alone. -/
theorem bTerm_left_succ_zero (X : TopCat.{0}) (k a' b q M' : ℕ) {d : ℕ}
    (ρ : singularSimplices X (M' + 1)) (τ : singularSimplices X d) :
    padFourL X k (a' + 1) b (phiAtDeg X (a' + 1) 0 ρ)
        ((groupRingGen ^ 0) • phiAtDeg X b q τ)
      = padFour X k a' b
          (∑ jj : Fin (M' + 2), phiAtDeg X a' 0 (faceSimplex X M' jj ρ))
          ((groupRingGen ^ 0) • phiAtDeg X b q τ) := by
  rw [padFourL_bTerm_succ, dTgt_phiAtDeg_zero X a' M' ρ]

/-- **Right block, index a successor.**  The generator power passes the
differential, so the `(1 + T)` part appears underneath it. -/
theorem bTerm_right_succ_succ (X : TopCat.{0}) (k a b' p q' M'' : ℕ) {c : ℕ}
    (ρ : singularSimplices X c) (τ : singularSimplices X (M'' + 1)) :
    padFourR X k a (b' + 1) (phiAtDeg X a p ρ)
        ((groupRingGen ^ p) • phiAtDeg X (b' + 1) (q' + 1) τ)
      = padFour X k a b' (phiAtDeg X a p ρ)
          ((groupRingGen ^ p) •
            ((phiAtDeg X b' q' τ + swapEnd X b' (phiAtDeg X b' q' τ))
              + ∑ jj : Fin (M'' + 2), phiAtDeg X b' (q' + 1) (faceSimplex X M'' jj τ))) := by
  rw [padFourR_bTerm_succ, dTgt_phiAtDeg_succ X b' q' M'' τ]

/-- **Right block, index zero.** -/
theorem bTerm_right_succ_zero (X : TopCat.{0}) (k a b' p M'' : ℕ) {c : ℕ}
    (ρ : singularSimplices X c) (τ : singularSimplices X (M'' + 1)) :
    padFourR X k a (b' + 1) (phiAtDeg X a p ρ)
        ((groupRingGen ^ p) • phiAtDeg X (b' + 1) 0 τ)
      = padFour X k a b' (phiAtDeg X a p ρ)
          ((groupRingGen ^ p) •
            ∑ jj : Fin (M'' + 2), phiAtDeg X b' 0 (faceSimplex X M'' jj τ)) := by
  rw [padFourR_bTerm_succ, dTgt_phiAtDeg_zero X b' M'' τ]

/-- **Left block vanishing**, when the face it differentiates cannot carry its
index. -/
theorem bTerm_left_small (X : TopCat.{0}) (k a b p q : ℕ) {c d : ℕ}
    (ρ : singularSimplices X c) (τ : singularSimplices X d) (h : c < p) :
    padFourL X k a b (phiAtDeg X a p ρ)
        ((groupRingGen ^ p) • phiAtDeg X b q τ) = 0 := by
  rw [phiAtDeg_eq_zero_of_lt X a p c ρ h]
  exact padFourL_of_zero_left X k a b _

/-- **Right block vanishing**, by the mirror. -/
theorem bTerm_right_small (X : TopCat.{0}) (k a b p q : ℕ) {c d : ℕ}
    (ρ : singularSimplices X c) (τ : singularSimplices X d) (h : d < q) :
    padFourR X k a b (phiAtDeg X a p ρ)
        ((groupRingGen ^ p) • phiAtDeg X b q τ) = 0 := by
  rw [phiAtDeg_eq_zero_of_lt X b q d τ h, smul_zero]
  exact padFourR_of_zero_right X k a b _

end

end Steenrod
end CharClass
end GroupApproximation
