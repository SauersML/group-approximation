import GroupApproximation.CharClass.SteenrodFourfoldBLeft

/-!
# The right block of `B`'s Leibniz rule, expanded

The mirror of the left block, with one extra step: the second factor carries a
power of the generator, and the differential has to be moved past it before the
boundary identity applies.  That is `dTgt_smul`, the group-ring linearity of the
pair differential, and it is the only place the power of the generator interacts
with anything.

Degrees are written with the successor outermost throughout, for the reason
recorded in the left-block file: `rw` will not match `?a + 1` against a sum whose
second summand is the successor.

## Main results

* `padFourR_compBPre_succ` — back index a successor: the `(1 + T)` part and the
  face-sum part, both under the generator power.
* `padFourR_compBPre_zero` — back index `0`: the face-sum part alone.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-- **Back index a successor.**  The power of the generator commutes with the
differential, so the boundary identity applies underneath it. -/
theorem padFourR_compBPre_succ (X : TopCat.{0}) (k a M' q' p : ℕ)
    (u : PairIdx X a →₀ ZMod 2) (σ'' : singularSimplices X (M' + 1)) :
    padFourR X k a (M' + 1 + q' + 1) u
        ((groupRingGen ^ p) • phiAtDeg X (M' + 1 + q' + 1) (q' + 1) σ'')
      = padFour X k a (M' + 1 + q') u
          ((groupRingGen ^ p) •
            ((phiAtDeg X (M' + 1 + q') q' σ''
                + swapEnd X (M' + 1 + q') (phiAtDeg X (M' + 1 + q') q' σ''))
              + ∑ jj : Fin (M' + 2),
                  phiAtDeg X (M' + 1 + q') (q' + 1) (faceSimplex X M' jj σ''))) := by
  rw [padFourR_succ_eq', dTgt_smul, dTgt_phiAtDeg_succ X (M' + 1 + q') q' M' σ'']

/-- **Back index `0`.**  No low part, for the same reason as on the left. -/
theorem padFourR_compBPre_zero (X : TopCat.{0}) (k a M' p : ℕ)
    (u : PairIdx X a →₀ ZMod 2) (σ'' : singularSimplices X (M' + 1)) :
    padFourR X k a (M' + 1) u
        ((groupRingGen ^ p) • phiAtDeg X (M' + 1) 0 σ'')
      = padFour X k a M' u
          ((groupRingGen ^ p) •
            ∑ jj : Fin (M' + 2), phiAtDeg X M' 0 (faceSimplex X M' jj σ'')) := by
  rw [padFourR_succ_eq', dTgt_smul, dTgt_phiAtDeg_zero X M' M' σ'']

end

end Steenrod
end CharClass
end GroupApproximation
