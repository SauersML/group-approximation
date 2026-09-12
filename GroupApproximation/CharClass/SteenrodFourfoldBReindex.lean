import GroupApproximation.CharClass.SteenrodFourfoldBEdge

/-!
# The reindexing, instantiated

Of the four families the differential produces, two survive the edge vanishings
and then cancel against each other.  This file names them and does the
cancellation.

The left family at splitting `p + 1` carries `Φ(e_p ⊗ ρ)` against
`t^{p+1} Φ(e_{i-p} ⊗ τ)`; the right family at splitting `p` carries exactly the
same thing.  So the left family read one step later *is* the right family, and
the left family contributes nothing at splitting `0`, because there is no
boundary to take there.  Two sums that agree after a shift, one of them starting
at zero, cancel in characteristic two — which is `sum_shift_cancel`.

Naming the families as a definition rather than inlining them is what makes the
shift identity `rfl`: the shifted left family and the right family are the same
expression, not merely equal ones.

## Main results

* `cancelA`, `cancelB` — the two surviving families.
* `cancelA_succ` — the shift identity, definitional.
* `sum_cancelA_cancelB` — **they cancel.**
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

variable {X : TopCat.{0}}

/-- The surviving left family: the low part of the left block, which is absent at
splitting `0`. -/
noncomputable def cancelA (X : TopCat.{0}) (k i c d : ℕ)
    (ρ : singularSimplices X c) (τ : singularSimplices X d) :
    ℕ → (TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2)
  | 0 => 0
  | p + 1 =>
      padFour X k (c + p) (d + (i - p)) (phiAtDeg X (c + p) p ρ)
        ((groupRingGen ^ (p + 1)) • phiAtDeg X (d + (i - p)) (i - p) τ)

/-- The surviving right family: the half of the low part of the right block that
carries the higher power of the generator. -/
noncomputable def cancelB (X : TopCat.{0}) (k i c d : ℕ)
    (ρ : singularSimplices X c) (τ : singularSimplices X d) (p : ℕ) :
    TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2 :=
  padFour X k (c + p) (d + (i - p)) (phiAtDeg X (c + p) p ρ)
    ((groupRingGen ^ (p + 1)) • phiAtDeg X (d + (i - p)) (i - p) τ)

/-- **The shift identity**, and it is definitional: the left family read one step
later is the right family, not merely equal to it. -/
theorem cancelA_succ (X : TopCat.{0}) (k i c d : ℕ)
    (ρ : singularSimplices X c) (τ : singularSimplices X d) (p : ℕ) :
    cancelA X k i c d ρ τ (p + 1) = cancelB X k i c d ρ τ p := rfl

theorem cancelA_zero (X : TopCat.{0}) (k i c d : ℕ)
    (ρ : singularSimplices X c) (τ : singularSimplices X d) :
    cancelA X k i c d ρ τ 0 = 0 := rfl

/-- **The cancellation.**  The two surviving families sum to zero. -/
theorem sum_cancelA_cancelB (X : TopCat.{0}) (k i c d n : ℕ)
    (ρ : singularSimplices X c) (τ : singularSimplices X d) :
    (∑ p ∈ Finset.range (n + 1), cancelA X k i c d ρ τ p)
        + ∑ p ∈ Finset.range n, cancelB X k i c d ρ τ p = 0 :=
  sum_shift_cancel n (cancelA X k i c d ρ τ) (cancelB X k i c d ρ τ)
    (cancelA_succ X k i c d ρ τ) (cancelA_zero X k i c d ρ τ)

end

end Steenrod
end CharClass
end GroupApproximation
