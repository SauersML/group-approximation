import GroupApproximation.CharClass.LIXLocalPair
import GroupApproximation.CharClass.RelativeProdContractible

/-!
# The local-model identification, unconditional

Lane `cc-lix-odd`.

`LIXLocalPair` carried `cc-relative`'s product-pair corollary as the named hypothesis
`hprod`.  That corollary has landed in the agreed signature, so this file discharges it by
one application and nothing else moves.

The contractibility it wants is `contractibleSpace_lixTrivBall`, and the point it wants is
the section's zero, which lies in the ball by construction.  The degree hypothesis is free:
the degree is twice the rank, and the rank is the tower sum plus three.

## Main result

* `lixLocalPairIsoClosed` — **the bundle pair over the neighbourhood, identified with the
  local model, with no hypotheses.**
-/

noncomputable section

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

/-- The section's zero, as a point of the contractible neighbourhood. -/
def lixZeroInBall (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    ↥(lixTrivBall hGc hGu) :=
  ⟨lixZero dd, lixZero_mem_lixBaseBall _ _ _⟩

theorem two_le_two_mul_lixRank (dd : Fin ℓ → ℕ) : 2 ≤ 2 * lixRank dd := by
  have h : 3 ≤ lixRank dd := by
    rw [lixRank]
    omega
  omega

/-- **The identification with the local model, unconditional.** -/
def lixLocalPairIsoClosed (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    relCohomology (ZMod 2)
        (TopCat.of (Bundle.Total
          ((lixBundle G hGc hGu).restrictTo (lixTrivBall hGc hGu))))
        {w : Bundle.Total ((lixBundle G hGc hGu).restrictTo (lixTrivBall hGc hGu)) |
          (w : ↥(lixTrivBall hGc hGu) × (VIdx dd ⊕ VIdx dd → ℂ))
            ∈ Bundle.puncturedSet
              ((lixBundle G hGc hGu).restrictTo (lixTrivBall hGc hGu))}
        (2 * lixRank dd)
      ≅ relCohomology (ZMod 2) (TopCat.of (Fin (lixRank dd) → ℂ))
        (puncturedSet (lixRank dd)) (2 * lixRank dd) :=
  lixLocalPairIso hGc hGu (2 * lixRank dd)
    (RelativeSupport.relCohomologyProdIso (contractibleSpace_lixTrivBall hGc hGu)
      (lixZeroInBall hGc hGu) (lixRank dd) (2 * lixRank dd)
      (two_le_two_mul_lixRank dd))

end GroupApproximation.CharClass
