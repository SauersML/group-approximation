import GroupApproximation.CharClass.LIXBaseBall
import GroupApproximation.CharClass.LIXBundleModel
import GroupApproximation.CharClass.BundleTotalOn
import GroupApproximation.CharClass.RelativeLocal
import GroupApproximation.CharClass.RelativeLocalModel

/-!
# The bundle pair over a contractible neighbourhood, identified with the local model

Lane `cc-lix-odd`.

Three landed pieces and one named hypothesis compose here.

* `cc-bundle`'s `totalTrivStdOn` trivialises the mapping torus over any subset of a
  trivialising set, with `totalTrivStdOn_image_punctured` giving the pair statement in the
  image form a congruence consumes.
* `LIXBaseBall` supplies a **contractible** open neighbourhood of the section's zero inside
  that trivialising set; the trivialising set itself is not contractible, which is why the
  shrinking step exists.
* `cc-relative`'s congruence turns the trivialisation into an isomorphism of relative
  groups.
* The last step, the product pair over a contractible base against the local model, is
  `cc-relative`'s corollary, taken here as the named hypothesis `hprod` until their probe
  is green.

## Main results

* `lixTrivBall` — the contractible neighbourhood, inside the trivialising set at the zero.
* `lixBundlePairIso` — the bundle pair over it, as a product pair.
* `lixLocalPairIso` — **the identification with the local model**, over `hprod`.
-/

noncomputable section

namespace GroupApproximation.CharClass

open Set CategoryTheory
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

/-! ## 1. The neighbourhood, inside the trivialising set -/

/-- The trivialising set of the mapping torus at the section's zero. -/
def lixTrivSet (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    Set (↥sphereOne × baseM dd) :=
  Bundle.trivSet (lixBundle G hGc hGu) (lixZero dd)

theorem isOpen_lixTrivSet (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) : IsOpen (lixTrivSet hGc hGu) :=
  Bundle.isOpen_trivSet _ _

theorem lixZero_mem_lixTrivSet (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) : lixZero dd ∈ lixTrivSet hGc hGu :=
  Bundle.self_mem_trivSet _ _

/-- **The contractible neighbourhood the whole argument runs over.** -/
def lixTrivBall (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    Set (↥sphereOne × baseM dd) :=
  lixBaseBall dd (lixTrivSet hGc hGu) (isOpen_lixTrivSet hGc hGu)
    (lixZero_mem_lixTrivSet hGc hGu)

theorem lixTrivBall_subset (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    lixTrivBall hGc hGu ⊆ Bundle.trivSet (lixBundle G hGc hGu) (lixZero dd) :=
  lixBaseBall_subset _ _ _

/-- The chart cut to the ball has the neighbourhood as its target.  `lixBaseBall` is
defined as an image and the contractibility proof is stated at the target, so the two must
be identified; they agree because a partial homeomorphism carries its source onto its
target. -/
theorem lixBallChart_target_eq (U : Set (↥sphereOne × baseM dd)) (hU : IsOpen U)
    (hzU : lixZero dd ∈ U) :
    (lixBallChart dd U hU hzU).target = lixBaseBall dd U hU hzU := by
  rw [← (lixBallChart dd U hU hzU).image_source_eq_target, lixBallChart_source]
  rfl

theorem contractibleSpace_lixTrivBall (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    ContractibleSpace ↥(lixTrivBall hGc hGu) := by
  have h := contractibleSpace_lixBallChart_target (dd := dd) (lixTrivSet hGc hGu)
    (isOpen_lixTrivSet hGc hGu) (lixZero_mem_lixTrivSet hGc hGu)
  rwa [lixBallChart_target_eq] at h

/-! ## 2. The bundle pair over it, as a product pair -/

/-- **The bundle pair over the neighbourhood is a product pair.**  `cc-bundle`'s
trivialisation over a subset, read through `cc-relative`'s congruence. -/
def lixBundlePairIso (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (n : ℕ) :
    relCohomology (ZMod 2)
        (TopCat.of (Bundle.Total
          ((lixBundle G hGc hGu).restrictTo (lixTrivBall hGc hGu))))
        {w : Bundle.Total ((lixBundle G hGc hGu).restrictTo (lixTrivBall hGc hGu)) |
          (w : ↥(lixTrivBall hGc hGu) × (VIdx dd ⊕ VIdx dd → ℂ))
            ∈ Bundle.puncturedSet
              ((lixBundle G hGc hGu).restrictTo (lixTrivBall hGc hGu))} n
      ≅ relCohomology (ZMod 2)
        (TopCat.of (↥(lixTrivBall hGc hGu) × (Fin (lixRank dd) → ℂ)))
        {q : ↥(lixTrivBall hGc hGu) × (Fin (lixRank dd) → ℂ) | q.2 ≠ 0} n :=
  relCohomologyCongr
    (Bundle.totalTrivStdOn (lixBundle G hGc hGu) (lixZero dd) (lixTrivBall hGc hGu)
      (lixTrivBall_subset hGc hGu) (lixRank dd) (rank_lixBundle G hGc hGu _)) _ _
    (Bundle.totalTrivStdOn_image_punctured (lixBundle G hGc hGu) (lixZero dd)
      (lixTrivBall hGc hGu) (lixTrivBall_subset hGc hGu) (lixRank dd)
      (rank_lixBundle G hGc hGu _)) n

/-! ## 3. The identification with the local model -/

/-- **The bundle pair over the neighbourhood, identified with the local model.**

`hprod` is `cc-relative`'s corollary, in the shape they announced; when their probe is
green this becomes one application and nothing else here moves. -/
def lixLocalPairIso (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (n : ℕ)
    (hprod : relCohomology (ZMod 2)
        (TopCat.of (↥(lixTrivBall hGc hGu) × (Fin (lixRank dd) → ℂ)))
        {q : ↥(lixTrivBall hGc hGu) × (Fin (lixRank dd) → ℂ) | q.2 ≠ 0} n
      ≅ relCohomology (ZMod 2) (TopCat.of (Fin (lixRank dd) → ℂ))
        (puncturedSet (lixRank dd)) n) :
    relCohomology (ZMod 2)
        (TopCat.of (Bundle.Total
          ((lixBundle G hGc hGu).restrictTo (lixTrivBall hGc hGu))))
        {w : Bundle.Total ((lixBundle G hGc hGu).restrictTo (lixTrivBall hGc hGu)) |
          (w : ↥(lixTrivBall hGc hGu) × (VIdx dd ⊕ VIdx dd → ℂ))
            ∈ Bundle.puncturedSet
              ((lixBundle G hGc hGu).restrictTo (lixTrivBall hGc hGu))} n
      ≅ relCohomology (ZMod 2) (TopCat.of (Fin (lixRank dd) → ℂ))
        (puncturedSet (lixRank dd)) n :=
  (lixBundlePairIso hGc hGu n).trans hprod

end GroupApproximation.CharClass
