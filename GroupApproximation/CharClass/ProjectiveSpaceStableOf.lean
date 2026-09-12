import GroupApproximation.CharClass.ChernEulerIso
import GroupApproximation.CharClass.MayerVietorisPullOf
import GroupApproximation.CharClass.ProjectiveSpaceComputationOf

/-!
# The hyperplane and block inclusions are bijective on `H^2(-; K)`

The coefficient-generic form of `ProjectiveSpaceStable` §1–2, carried along the iterated inclusion
of `ProjectiveSpaceIterate` and the block inclusion of `ChernEulerIso`.

Over `F₂` stability of the generator is a statement about one element, because an `F₂`-line has
exactly one nonzero element.  Over a field `K` there is no canonical generator, so what is carried
over is the statement underneath it: pullback along `ℂP^d ⊆ ℂP^{d+1}` is **bijective** in degree
two for `d ≥ 1`.  The proof is the `F₂` one with every input replaced by its `K` form:

* the retraction of the punctured space is a homotopy equivalence, so pullback along
  `ℂP^d ⊆ ℂP^{d+1} ∖ {pt}` is bijective in every degree (`pullEquivOfHomotopyEquivOf`);
* the Mayer–Vietoris restriction to the punctured space is bijective in degree two, because the
  chart has no `H^2` and the intersection is `S^{2d+1}` (`mvSequenceOf`,
  `hasPointCohomologyOf_chartSpace`, `hasSphereCohomologyOf_interSpace`);
* that restriction is a pullback (`mvResVOf_eq_pull`).

Iterating gives the `k`-fold inclusion.  The block inclusion `cpBlockInclIter d` is homotopic to
the `(d+1)`-fold one (`homotopic_cpBlockInclIter`, which is coefficient-free), so it is bijective
on `H^2(-; K)` as well.

## Main declarations

* `bijective_pull_cpInclPOf`, `resVOf_eq_pull`, `bijective_resVOf_two`,
  `bijective_pull_punctInclOf_two`.
* `bijective_pull_cpInclOf` — the hyperplane inclusion is bijective on `H^2(-; K)`.
* `bijective_pull_cpInclIterOf` — and so is the iterated one.
* `bijective_pull_cpBlockInclIterOf` — **and so is the block inclusion**, which is what
  `ChernEulerIsoOf` consumes.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace CPn

open CategoryTheory TopologicalSpace
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.CharClass.Bundle

noncomputable section

/-! ## 1. The two halves of the hyperplane inclusion -/

/-- Pullback along `ℂP^d ⊆ ℂP^{d+1} ∖ {pt}` is bijective in every degree, over `K`: it is the
inverse of the homotopy equivalence given by the retraction. -/
theorem bijective_pull_cpInclPOf (K : Type) [CommRing K] (d n : ℕ) :
    Function.Bijective (pull (K := K) (cpInclP d) n) :=
  (pullEquivOfHomotopyEquivOf K (punctOpenHomotopyEquiv d) n).symm.bijective

/-- The Mayer–Vietoris restriction to the punctured space is a pullback, over `K`. -/
theorem resVOf_eq_pull (K : Type) [Field K] (d n : ℕ) (a : Hmod K (CPtop (d + 1)) n) :
    (mvSequenceOf K (chartOpen d) (punctOpen d) (chartOpen_sup_punctOpen d)).resV n a
      = pull (punctIncl d) n a := by
  show (mvResVOf K (chartOpen d) (punctOpen d) (chartOpen_sup_punctOpen d) n).hom a = _
  rw [mvResVOf_eq_pull]
  rfl

/-- Restriction to the punctured space is bijective in degree 2 for `d ≥ 1`, over `K`.  The chart
has no `H^2`, and the intersection is a sphere of dimension `2d+1`, which is neither `1` nor `2`. -/
theorem bijective_resVOf_two (K : Type) [Field K] (d : ℕ) (hd : 1 ≤ d) :
    Function.Bijective
      ((mvSequenceOf K (chartOpen d) (punctOpen d) (chartOpen_sup_punctOpen d)).resV 2) := by
  refine MVSequenceOf.bijective_resV _ 1 ?_ ?_ ?_
  · exact fun a => (hasPointCohomologyOf_chartSpace K d).2 2 (by omega) a
  · exact fun w => (hasSphereCohomologyOf_interSpace K d).2.2 1 (by omega) (by omega) w
  · exact fun w => (hasSphereCohomologyOf_interSpace K d).2.2 2 (by omega) (by omega) w

theorem bijective_pull_punctInclOf_two (K : Type) [Field K] (d : ℕ) (hd : 1 ≤ d) :
    Function.Bijective (pull (K := K) (punctIncl d) 2) := by
  have hb := bijective_resVOf_two K d hd
  have heq : ⇑((mvSequenceOf K (chartOpen d) (punctOpen d) (chartOpen_sup_punctOpen d)).resV 2)
      = pull (K := K) (punctIncl d) 2 :=
    funext (resVOf_eq_pull K d 2)
  rwa [heq] at hb

/-- **The hyperplane inclusion is bijective on `H^2(-; K)`**, for `d ≥ 1`. -/
theorem bijective_pull_cpInclOf (K : Type) [Field K] (d : ℕ) (hd : 1 ≤ d) :
    Function.Bijective (pull (K := K) (cpIncl d) 2) := by
  have hfun : pull (K := K) (cpIncl d) 2
      = (pull (cpInclP d) 2) ∘ (pull (punctIncl d) 2) :=
    funext fun a => pull_comp _ _ 2 a
  rw [hfun]
  exact Function.Bijective.comp (bijective_pull_cpInclPOf K d 2)
    (bijective_pull_punctInclOf_two K d hd)

/-! ## 2. The iterated and the block inclusions -/

/-- **The iterated hyperplane inclusion is bijective on `H^2(-; K)`**, for `d ≥ 1`. -/
theorem bijective_pull_cpInclIterOf (K : Type) [Field K] (d : ℕ) (hd : 1 ≤ d) (k : ℕ) :
    Function.Bijective (pull (K := K) (cpInclIter d k) 2) := by
  induction k with
  | zero =>
    have hfun : pull (K := K) (cpInclIter d 0) 2 = id := funext fun a => pull_id 2 a
    rw [hfun]
    exact Function.bijective_id
  | succ k ih =>
    have hfun : pull (K := K) (cpInclIter d (k + 1)) 2
        = (pull (cpInclIter d k) 2) ∘ (pull (cpIncl (d + k)) 2) :=
      funext fun a => pull_comp _ _ 2 a
    rw [hfun]
    exact ih.comp (bijective_pull_cpInclOf K (d + k) (by omega))

/-- **The block inclusion is bijective on `H^2(-; K)`**, for `d ≥ 1`: it is homotopic to the
`(d+1)`-fold hyperplane inclusion. -/
theorem bijective_pull_cpBlockInclIterOf (K : Type) [Field K] (d : ℕ) (hd : 1 ≤ d) :
    Function.Bijective (pull (K := K) (cmap (cpBlockInclIter d)) 2) := by
  have hfun : pull (K := K) (cmap (cpBlockInclIter d)) 2 = pull (cpInclIter d (d + 1)) 2 := by
    funext a
    rw [cpInclIter_eq_cmap_cpEmbed d (d + 1)]
    exact pull_eq_of_homotopicOf K (f := cmap (cpBlockInclIter d))
      (g := cmap (cpEmbed (iterMat d (d + 1)) (iterMat_isometry d (d + 1))))
      (homotopic_cpBlockInclIter d) 2 a
  rw [hfun]
  exact bijective_pull_cpInclIterOf K d hd (d + 1)

end

end CPn
end CharClass
end GroupApproximation
