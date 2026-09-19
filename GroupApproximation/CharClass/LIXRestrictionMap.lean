import GroupApproximation.CharClass.LIXLocalPairClosed
import GroupApproximation.CharClass.LIXBundlePair
import GroupApproximation.CharClass.BundleTotalOver
import GroupApproximation.CharClass.RelativeFunctorial
import GroupApproximation.CharClass.CohomologyBridge

/-!
# The restriction of the bundle pair to the trivialising neighbourhood

Lane `cc-lix-odd`, the `res` argument of `cc-thom`'s local form.

`totalInclOn` includes the total space of the bundle restricted to a subset into the whole
total space, and `totalInclOn_mem_puncturedSet_iff` says it is a map of punctured pairs in
**both** directions.  Pulling back on relative cohomology along it, which is contravariant,
gives the restriction

```text
H^n(E, E ∖ 0)  ⟶  H^n(E|_ball, E|_ball ∖ 0)
```

with `ball` this lane's contractible neighbourhood of the section's zero.

**This is a term with no properties attached, deliberately.**  `cc-thom` proves `hsq` and
`hres` against it, so its spelling is what they wait on and any property I guessed at here
would be one they had to work around.

**It is not excision**, and `cc-bundle`'s own docstring says why: excision needs a set whose
closure sits inside the punctured set, and any such set contains zero-section points, which
are exactly what the punctured set omits.  So the injectivity is `cc-thom`'s to prove by
another route, not mine to assert.

## Main result

* `lixRes` — **the restriction map**, in the target type of `lix_topClass_ne_zero_of_local`.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open CategoryTheory
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

/-- The inclusion is a map of pairs, in the form `relPullback` consumes. -/
theorem lixTotalInclOn_mapsTo (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    ∀ w ∈ {w : Bundle.Total
        ((lixBundle G hGc hGu).restrictTo (lixTrivBall hGc hGu)) |
        (w : ↥(lixTrivBall hGc hGu) × (VIdx dd ⊕ VIdx dd → ℂ))
          ∈ Bundle.puncturedSet
            ((lixBundle G hGc hGu).restrictTo (lixTrivBall hGc hGu))},
      (ConcreteCategory.hom
        (cmap (Bundle.totalInclOn (lixBundle G hGc hGu) (lixTrivBall hGc hGu)))) w
        ∈ lixPuncturedInTotal hGc hGu := by
  intro w hw
  exact (Bundle.totalInclOn_mem_puncturedSet_iff (lixBundle G hGc hGu)
    (lixTrivBall hGc hGu) w).mpr hw

/-- **The restriction of the bundle pair to the trivialising neighbourhood.** -/
def lixRes (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) (n : ℕ) :
    relCohomology (ZMod 2) (lixTotalPair hGc hGu) (lixPuncturedInTotal hGc hGu) n ⟶
      relCohomology (ZMod 2)
        (TopCat.of (Bundle.Total
          ((lixBundle G hGc hGu).restrictTo (lixTrivBall hGc hGu))))
        {w : Bundle.Total ((lixBundle G hGc hGu).restrictTo (lixTrivBall hGc hGu)) |
          (w : ↥(lixTrivBall hGc hGu) × (VIdx dd ⊕ VIdx dd → ℂ))
            ∈ Bundle.puncturedSet
              ((lixBundle G hGc hGu).restrictTo (lixTrivBall hGc hGu))} n :=
  relPullback (ZMod 2)
    (cmap (Bundle.totalInclOn (lixBundle G hGc hGu) (lixTrivBall hGc hGu)))
    (lixTotalInclOn_mapsTo hGc hGu) n

end GroupApproximation.CharClass
