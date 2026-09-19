import GroupApproximation.CharClass.SteenrodFourfoldBRight
import GroupApproximation.CharClass.CartanMidFourChainMap

/-!
# Transporting the computation through the interchange

The chain-map identity for `B` is proved on `compBPre`, the value before the
middle interchange, and transported afterwards.  This file is the transport, and
it is unconditional: the three facts it needs are all available, so it can be
stated and proved before the computation it will carry.

* `compBGen` **is** the interchange of the pre-interchange value, because the
  interchange is linear and a linear map passes through a linear combination.
* The differential commutes with the interchange, which is `cc-cartan`'s
  `tensorD_midSwap`, on arbitrary chains.
* The interchange carries the action that swaps *inside* each block to the action
  that *exchanges* the blocks, which is their `midSwap_blockSwap`.  That is the
  conjugation the whole design turns on, and it is the reason the composite
  intertwines the generator with `(13)(24)` rather than `(12)(34)`.

With these, the chain-map identity for `compBGen` follows from the identity for
`compBPreGen` by applying the interchange to both sides.

## Main results

* `compBPreGen`, `compBGen_eq_midSwap` — the pre-interchange value and its place.
* `tensorD_compBGen_eq` — the differential of `B` is the interchange of the
  differential of the pre-interchange value.
* `midSwap_innerSwap` — the conjugation, in this lane's names.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-- `B` on a basis element, **before** the middle interchange. -/
noncomputable def compBPreGen (X : TopCat.{0}) (k i : ℕ) {N : ℕ}
    (σ : singularSimplices X N) : TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2 :=
  ∑ p ∈ Finset.range (i + 1),
    Finsupp.linearCombination (ZMod 2) (compBPre X k i p N) (phiZero X N σ)

/-- **`B` is the interchange of the pre-interchange value.**  The interchange is
linear, so it passes through both the sum over the resolution index and the
linear combination over the basis of `Φ₀(σ)`. -/
theorem compBGen_eq_midSwap (X : TopCat.{0}) (k i : ℕ) {N : ℕ}
    (σ : singularSimplices X N) :
    compBGen X k i σ
      = midSwap (singFreeCx X) (singFreeCx X) (singFreeCx X) (singFreeCx X) k
          (compBPreGen X k i σ) := by
  unfold compBGen compBPreGen
  rw [map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  exact (apply_linearCombination'
    (midSwap (singFreeCx X) (singFreeCx X) (singFreeCx X) (singFreeCx X) k)
    (compBPre X k i p N) (phiZero X N σ)).symm

/-- **The differential of `B` is the interchange of the differential of the
pre-interchange value.**  So the whole computation may be done before the
interchange and carried across at the end. -/
theorem tensorD_compBGen_eq (X : TopCat.{0}) (k i : ℕ) {N : ℕ}
    (σ : singularSimplices X N) :
    tensorD (pairFreeCx X) (pairFreeCx X) k (compBGen X (k + 1) i σ)
      = midSwap (singFreeCx X) (singFreeCx X) (singFreeCx X) (singFreeCx X) k
          (tensorD (pairFreeCx X) (pairFreeCx X) k (compBPreGen X (k + 1) i σ)) := by
  rw [compBGen_eq_midSwap, tensorD_midSwap]

/-- The action that swaps inside each block, on the fourfold. -/
noncomputable def innerSwapFour (X : TopCat.{0}) (k : ℕ) :
    (TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2) →ₗ[ZMod 2]
      (TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2) :=
  tenHom (swapHom (singFreeCx X)) (swapHom (singFreeCx X)) k

/-- **The conjugation.**  The interchange carries swapping inside each block to
exchanging the blocks.  This is why the second composite intertwines the
generator with `(13)(24)`, and it is the one line the first version of `compB`
was missing. -/
theorem midSwap_innerSwap (X : TopCat.{0}) (k : ℕ)
    (y : TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2) :
    midSwap (singFreeCx X) (singFreeCx X) (singFreeCx X) (singFreeCx X) k
        (innerSwapFour X k y)
      = tenSwap (pairFreeCx X) k
          (midSwap (singFreeCx X) (singFreeCx X) (singFreeCx X) (singFreeCx X) k y) :=
  midSwap_blockSwap (singFreeCx X) k y

end

end Steenrod
end CharClass
end GroupApproximation
