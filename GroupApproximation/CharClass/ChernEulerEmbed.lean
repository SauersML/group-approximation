import GroupApproximation.CharClass.ChernEulerIso

/-!
# Composing a classifying map with a coordinate embedding leaves the Euler class alone

The class identification compares two rank-one bundles whose index types have
different sizes, by pushing both into a common larger one.  For that to be free in
cohomology, the push must not move the Euler class, and this is that statement in
the form the comparison uses: composing a classifying map with the iterated
coordinate embedding changes nothing.

It is two lines, because the embedding is the iterated hyperplane inclusion in
`cc-bundle`'s spelling and that inclusion fixes the degree-two generator.

## Main declarations

* `pull_cpEmbed_iterMat_cpGen` — the embedding fixes the generator.
* `eulerClass_cpEmbed_iterMat` — **so it leaves an Euler class alone**.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace CPn

open CategoryTheory
open GroupApproximation.CharClass.Bundle

noncomputable section

/-- The iterated coordinate embedding fixes the degree-two generator. -/
theorem pull_cpEmbed_iterMat_cpGen (a k : ℕ) (ha : 1 ≤ a) :
    pull (cmap (cpEmbed (iterMat a k) (iterMat_isometry a k))) 2
        (cpGen (a + k) (by omega))
      = cpGen a ha := by
  rw [← cpInclIter_eq_cmap_cpEmbed]
  exact pull_cpInclIter_cpGen a ha k

/-- **Composing a classifying map with the iterated coordinate embedding leaves the
Euler class alone.**  This is what makes pushing two bundles into a common larger
index free in cohomology. -/
theorem eulerClass_cpEmbed_iterMat {X : TopCat.{0}} (a k : ℕ) (ha : 1 ≤ a)
    (g : X ⟶ CPtop a) :
    eulerClass (cpGen (a + k) (by omega))
        (g ≫ cmap (cpEmbed (iterMat a k) (iterMat_isometry a k)))
      = eulerClass (cpGen a ha) g := by
  rw [eulerClass, eulerClass, pull_comp, pull_cpEmbed_iterMat_cpGen a k ha]

end

end CPn
end CharClass
end GroupApproximation
