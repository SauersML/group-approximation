import GroupApproximation.CharClass.SteenrodFourfoldBNat

/-!
# The left block of `B`'s Leibniz rule, expanded

The chain-map computation for `B` does not need the middle interchange at all.
`compBTerm` is `midSwap` of `compBPre`, `midSwap` is linear, and the whole
substantive identity can be proved on `compBPre` and transported afterwards.  So
this file and the next work entirely in this lane's vocabulary.

Here is the left block.  Differentiating the front factor of one term produces
the boundary identity for `Φ` at the index that factor carries, which has a
`(1 + T)` part exactly when the index is a successor and a face-sum part always.

The degrees are written with the successor **outermost**, `M + 1 + p' + 1`
rather than `M + 1 + (p' + 1)`: the two are definitionally equal, but `rw` will
not match `?a + 1` against a sum whose second summand is the successor, so a
lemma stated the other way round cannot be applied.
Two of the four cases are the vanishings of the previous file: the block dies
when the front face is too small to carry its share of the index, and when the
first degree is `0` there is no boundary to take.

## Main results

* `padFourL_compBPre_succ` — front index a successor: the `(1 + T)` part and the
  face-sum part.
* `padFourL_compBPre_zero` — front index `0`: the face-sum part alone.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-- **Front index a successor.**  The boundary of `Φ(e_{p+1} ⊗ σ')` is
`(1 + T) Φ(e_p ⊗ σ')` plus `Φ(e_{p+1} ⊗ ∂σ')`, so the left block splits into the
low part and the face-sum part. -/
theorem padFourL_compBPre_succ (X : TopCat.{0}) (k M p' b : ℕ)
    (σ' : singularSimplices X (M + 1)) (v : PairIdx X b →₀ ZMod 2) :
    padFourL X k (M + 1 + p' + 1) b
        (phiAtDeg X (M + 1 + p' + 1) (p' + 1) σ') v
      = padFour X k (M + 1 + p') b
          ((phiAtDeg X (M + 1 + p') p' σ'
              + swapEnd X (M + 1 + p') (phiAtDeg X (M + 1 + p') p' σ'))
            + ∑ jj : Fin (M + 2),
                phiAtDeg X (M + 1 + p') (p' + 1) (faceSimplex X M jj σ')) v := by
  rw [padFourL_succ_eq', dTgt_phiAtDeg_succ X (M + 1 + p') p' M σ']

/-- **Front index `0`.**  At the Alexander–Whitney end there is no low part. -/
theorem padFourL_compBPre_zero (X : TopCat.{0}) (k M b : ℕ)
    (σ' : singularSimplices X (M + 1)) (v : PairIdx X b →₀ ZMod 2) :
    padFourL X k (M + 1) b (phiAtDeg X (M + 1) 0 σ') v
      = padFour X k M b
          (∑ jj : Fin (M + 2), phiAtDeg X M 0 (faceSimplex X M jj σ')) v := by
  rw [padFourL_succ_eq', dTgt_phiAtDeg_zero X M M σ']

/-- The left block dies when the front face is a `0`-simplex and the index is
positive: there is no cut set that large. -/
theorem padFourL_compBPre_small (X : TopCat.{0}) (k p b : ℕ)
    (σ' : singularSimplices X 0) (v : PairIdx X b →₀ ZMod 2) (hp : 0 < p) :
    padFourL X k (0 + p) b (phiAtDeg X (0 + p) p σ') v = 0 :=
  padFourL_term_eq_zero X k 0 p b σ' v hp

end

end Steenrod
end CharClass
end GroupApproximation
