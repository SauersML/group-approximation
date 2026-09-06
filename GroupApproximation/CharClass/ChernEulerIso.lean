import GroupApproximation.CharClass.BundleBlockIter
import GroupApproximation.CharClass.ChernEulerBundle

/-!
# The Euler class is an invariant of the isomorphism class

Item 2 of this lane's brief, closed.  Two isomorphic line bundles need not have
homotopic classifying maps into the same projective space, which is why the naive
argument fails; they do after both are pushed into a large enough one, and
`cc-bundle`'s rotation supplies that homotopy.

What was missing on this side was the effect of that push on `H^2`.  The block
inclusion is homotopic to the iterated hyperplane inclusion, because their ranges
are disjoint coordinate blocks, and the iterated hyperplane inclusion carries the
generator to the generator by `pull_cpInclIter_cpGen`.  So the push is invisible
in degree two and the invariance follows.

The index types agree on the nose: `cc-bundle` restated the block inclusion at
`d + (d + 1)` rather than `2 * d + 1`, so no `Fin` congruence appears anywhere.

## Main declarations

* `cpInclIter_eq_cmap_cpEmbed` — the iterated inclusion is the coordinate embedding.
* `pull_cpBlockInclIter_cpGen` — the block inclusion fixes the generator.
* `eulerOfBundle_eq_of_bundleIso` — **the Euler class is an isomorphism invariant**.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace CPn

open CategoryTheory
open scoped Matrix
open GroupApproximation.STW59
open GroupApproximation.CharClass.Bundle

noncomputable section

/-- The coordinate embedding along the identity is the identity. -/
theorem cpEmbed_one (d : ℕ)
    (h : (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)ᴴ * 1 = 1) :
    cpEmbed (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) h = ContinuousMap.id (CP d) :=
  ContinuousMap.ext fun z => Subtype.ext (by
    rw [cpEmbed_apply, Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul]
    rfl)

/-- The hyperplane inclusion is the bundled `incl`. -/
theorem cpIncl_eq_cmap (d : ℕ) :
    cpIncl d = cmap (⟨incl, continuous_incl⟩ : C(CP d, CP (d + 1))) := rfl

/-- **The iterated hyperplane inclusion is the coordinate embedding**, which is
what lets the generator computation cross into `cc-bundle`'s vocabulary. -/
theorem cpInclIter_eq_cmap_cpEmbed (d k : ℕ) :
    cpInclIter d k = cmap (cpEmbed (iterMat d k) (iterMat_isometry d k)) := by
  induction k with
  | zero =>
    show 𝟙 (CPtop d)
      = cmap (cpEmbed (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) (iterMat_isometry d 0))
    rw [cpEmbed_one]
    rfl
  | succ k ih =>
    show cpInclIter d k ≫ cpIncl (d + k)
      = cmap (cpEmbed (iterMat d (k + 1)) (iterMat_isometry d (k + 1)))
    rw [cpEmbed_iterMat_succ, ih, cpIncl_eq_cmap, cpEmbed_shiftMat]
    rfl

/-- **The block inclusion fixes the degree-two generator.** -/
theorem pull_cpBlockInclIter_cpGen (d : ℕ) (hd : 1 ≤ d) :
    pull (cmap (cpBlockInclIter d)) 2 (cpGen (d + (d + 1)) (by omega)) = cpGen d hd := by
  have h : pull (cmap (cpBlockInclIter d)) 2 (cpGen (d + (d + 1)) (by omega))
      = pull (cmap (cpEmbed (iterMat d (d + 1)) (iterMat_isometry d (d + 1)))) 2
          (cpGen (d + (d + 1)) (by omega)) :=
    pull_eq_of_homotopic (f := cmap (cpBlockInclIter d))
      (g := cmap (cpEmbed (iterMat d (d + 1)) (iterMat_isometry d (d + 1))))
      (homotopic_cpBlockInclIter d) 2 _
  rw [h, ← cpInclIter_eq_cmap_cpEmbed d (d + 1)]
  exact pull_cpInclIter_cpGen d hd (d + 1)

/-- **The Euler class of a line bundle depends only on its isomorphism class.** -/
theorem eulerOfBundle_eq_of_bundleIso {X : Type} [TopologicalSpace X] {d : ℕ}
    (hd : 1 ≤ d) (p q : Bundle X (Fin (d + 1))) (hp : ∀ x, (p x).trace = 1)
    (hq : ∀ x, (q x).trace = 1) (e : BundleIso p q) :
    eulerOfBundle hd p hp = eulerOfBundle hd q hq := by
  have hgen := pull_cpBlockInclIter_cpGen d hd
  have h := pull_eq_of_homotopic
    (f := cmap ((cpBlockInclIter d).comp (classifyOne p hp)))
    (g := cmap ((cpBlockInclIter d).comp (classifyOne q hq)))
    (homotopic_classifyOne_blockInclIter hp hq e) 2
    (cpGen (d + (d + 1)) (by omega))
  show eulerClass (cpGen d hd) (cmap (classifyOne p hp))
    = eulerClass (cpGen d hd) (cmap (classifyOne q hq))
  rw [eulerClass, eulerClass, ← hgen, ← pull_comp, ← pull_comp]
  exact h

end

end CPn
end CharClass
end GroupApproximation
