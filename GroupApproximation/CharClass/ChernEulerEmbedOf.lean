import GroupApproximation.CharClass.ProjectiveSpaceStableOf
import GroupApproximation.CharClass.ChernEulerBundleOf

/-!
# The iterated coordinate embedding on `H^2(-; K)`

The coefficient-generic form of `ChernEulerEmbed`.  Over `F₂` the embedding fixes the generator.
Over a field `K` there is no generator to fix, and what carries over is the statement underneath
it: pullback along `ℂP^a ⊆ ℂP^{a+k}` is bijective on `H^2(-; K)` for `a ≥ 1`
(`ProjectiveSpaceStableOf.bijective_pull_cpInclIterOf`).  So a class on the big projective
space restricts to a class on the small one, nonzero exactly when it was nonzero, and composing a
classifying map with the embedding moves the chosen class instead of the map.

## Main declarations

* `bijective_pull_cpEmbed_iterMatOf` — the embedding is bijective on `H^2(-; K)`.
* `pull_cpEmbed_iterMat_ne_zeroOf` — **a nonzero class restricts to a nonzero class**.
* `eulerClassOf_cpEmbed_iterMat` — composing with the embedding pulls the class back.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace CPn

open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.CharClass.Bundle

noncomputable section

/-- **The iterated coordinate embedding is bijective on `H^2(-; K)`**, for `a ≥ 1`: it is the
iterated hyperplane inclusion in `cc-bundle`'s spelling. -/
theorem bijective_pull_cpEmbed_iterMatOf (K : Type) [Field K] (a k : ℕ) (ha : 1 ≤ a) :
    Function.Bijective
      (pull (K := K) (cmap (cpEmbed (iterMat a k) (iterMat_isometry a k))) 2) := by
  rw [← cpInclIter_eq_cmap_cpEmbed]
  exact bijective_pull_cpInclIterOf K a ha k

/-- **A nonzero class on `ℂP^{a+k}` restricts to a nonzero class on `ℂP^a`**, for `a ≥ 1`. -/
theorem pull_cpEmbed_iterMat_ne_zeroOf (K : Type) [Field K] (a k : ℕ) (ha : 1 ≤ a)
    (hgen : Hmod K (CPtop (a + k)) 2) (hgen0 : hgen ≠ 0) :
    pull (cmap (cpEmbed (iterMat a k) (iterMat_isometry a k))) 2 hgen ≠ 0 := by
  intro h
  apply hgen0
  refine (bijective_pull_cpEmbed_iterMatOf K a k ha).1 ?_
  rw [h, pull_zero]

/-- **Composing a classifying map with the iterated coordinate embedding pulls the chosen class
back along the embedding.**  Over `F₂` the pulled-back class is the generator again; over `K` it is
whatever `hgen` restricts to. -/
theorem eulerClassOf_cpEmbed_iterMat (K : Type) [CommRing K] {X : TopCat.{0}} (a k : ℕ)
    (hgen : Hmod K (CPtop (a + k)) 2) (g : X ⟶ CPtop a) :
    eulerClassOf K hgen (g ≫ cmap (cpEmbed (iterMat a k) (iterMat_isometry a k)))
      = eulerClassOf K (pull (cmap (cpEmbed (iterMat a k) (iterMat_isometry a k))) 2 hgen) g :=
  eulerClassOf_comp K hgen g _

end

end CPn
end CharClass
end GroupApproximation
