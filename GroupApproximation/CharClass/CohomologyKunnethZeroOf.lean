import GroupApproximation.CharClass.CohomologyKunnethStepOf
import GroupApproximation.CharClass.CohomologyKunnethZero
import GroupApproximation.Meta.AxiomGuard

/-!
# The base case of the Künneth induction over a field

Lane `lix-coeff` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.5).

Additive twin of `CohomologyKunnethZero` with coefficients in a field `K`.  `S⁰` is covered by its
two points, the cover `KnHemi.szPos`, `KnHemi.szNeg` of the `F₂` file (coefficient-free).  With an
empty intersection the matching condition of Mayer–Vietoris is vacuous, so there is a class
`zeroGenOf K` of `H⁰(S⁰; K)` restricting to `1` on the positive point and to `0` on the negative
one.  The class is obtained from `mvExactSumOf` and the vanishing of the cohomology of the empty
space, so no disjoint-cover splitting is needed.

The base case `knGen_zeroGenOf` is the `F₂` argument: restricting along the two slices gives
`v = c` and `0 = c`.  No sign and no inverse enter.

## Main declarations

* `KnHemi.zeroGenOf`, `KnHemi.mvResUOf_zeroGenOf`, `KnHemi.mvResVOf_zeroGenOf`.
* `KnHemi.pull_const_zeroGen_posOf`, `KnHemi.pull_const_zeroGen_negOf`.
* `KnHemi.knGen_zeroGenOf` — **the base of the Künneth induction over `K`**.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace KnHemi

/-! ## 1. The generator -/

/-- There is a class of `H⁰(S⁰; K)` restricting to `1` on the positive point and `0` on the
negative one: the two points are disjoint, so the matching condition is vacuous. -/
theorem exists_zeroGenOf (K : Type) [Field K] :
    ∃ x : Hmod K (TopCat.of (Sphere 0)) 0,
      (mvResUOf K szPos szNeg sz_sup 0).hom x = one (mvU szPos) ∧
        (mvResVOf K szPos szNeg sz_sup 0).hom x = 0 := by
  refine (mvExactSumOf K szPos szNeg sz_sup 0 (one (mvU szPos)) 0).1 ?_
  haveI := ModuleCat.subsingleton_of_isZero
    (isZero_cohomology_of_isEmptyOf K
      ↥((szPos : Set ↥(TopCat.of (Sphere 0))) ∩ (szNeg : Set ↥(TopCat.of (Sphere 0)))) 0)
  exact Subsingleton.elim _ _

/-- The class of `H⁰(S⁰; K)` that is `1` on the positive point and `0` on the negative one. -/
def zeroGenOf (K : Type) [Field K] : Hmod K (TopCat.of (Sphere 0)) 0 :=
  Classical.choose (exists_zeroGenOf K)

theorem mvResUOf_zeroGenOf (K : Type) [Field K] :
    (mvResUOf K szPos szNeg sz_sup 0).hom (zeroGenOf K) = one (mvU szPos) :=
  (Classical.choose_spec (exists_zeroGenOf K)).1

theorem mvResVOf_zeroGenOf (K : Type) [Field K] :
    (mvResVOf K szPos szNeg sz_sup 0).hom (zeroGenOf K) = 0 :=
  (Classical.choose_spec (exists_zeroGenOf K)).2

/-! ## 2. The two point evaluations -/

theorem pull_const_zeroGen_posOf (K : Type) [Field K] (Y : Type) [TopologicalSpace Y]
    (p : ↥(szPos : Set ↥(TopCat.of (Sphere 0)))) :
    pull (cmap (ContinuousMap.const Y (p : Sphere 0))) 0 (zeroGenOf K) = one (TopCat.of Y) := by
  have hres : pull (sInclusion (szPos : Set ↥(TopCat.of (Sphere 0)))) 0 (zeroGenOf K)
      = one (mvU szPos) := by
    rw [← cohPullbackK_apply_eq, ← mvResUOf_eq_pull K szPos szNeg sz_sup 0]
    exact mvResUOf_zeroGenOf K
  have hfac : (cmap (ContinuousMap.const Y (p : Sphere 0))
      : TopCat.of Y ⟶ TopCat.of (Sphere 0))
      = cmap (ContinuousMap.const Y p)
        ≫ sInclusion (szPos : Set ↥(TopCat.of (Sphere 0))) := rfl
  rw [hfac, pull_comp, hres, pull_one]

theorem pull_const_zeroGen_negOf (K : Type) [Field K] (Y : Type) [TopologicalSpace Y]
    (q : ↥(szNeg : Set ↥(TopCat.of (Sphere 0)))) :
    pull (cmap (ContinuousMap.const Y (q : Sphere 0))) 0 (zeroGenOf K) = 0 := by
  have hres : pull (sInclusion (szNeg : Set ↥(TopCat.of (Sphere 0)))) 0 (zeroGenOf K) = 0 := by
    rw [← cohPullbackK_apply_eq, ← mvResVOf_eq_pull K szPos szNeg sz_sup 0]
    exact mvResVOf_zeroGenOf K
  have hfac : (cmap (ContinuousMap.const Y (q : Sphere 0))
      : TopCat.of Y ⟶ TopCat.of (Sphere 0))
      = cmap (ContinuousMap.const Y q)
        ≫ sInclusion (szNeg : Set ↥(TopCat.of (Sphere 0))) := rfl
  rw [hfac, pull_comp, hres, pull_zero]

/-! ## 3. The base case -/

set_option maxHeartbeats 1000000 in
/-- **The base of the Künneth induction over `K`.** -/
theorem knGen_zeroGenOf (K : Type) [Field K] : KnGenOf K 0 (zeroGenOf K) := by
  intro Y _ m v c hc
  obtain ⟨p⟩ := nonempty_sphereZeroPos
  obtain ⟨q⟩ := nonempty_sphereZeroNeg
  have hp := congrArg (pull (knSlice Y 0 (p : Sphere 0)) (0 + m)) hc
  rw [pull_cup, pull_knSlice_knPrYOf, pull_knSlice_knPrYOf, pull_knSlice_knPrS_constOf,
    pull_const_zeroGen_posOf] at hp
  have hq := congrArg (pull (knSlice Y 0 (q : Sphere 0)) (0 + m)) hc
  rw [pull_cup, pull_knSlice_knPrYOf, pull_knSlice_knPrYOf, pull_knSlice_knPrS_constOf,
    pull_const_zeroGen_negOf, zero_cup] at hq
  have hone : cup (one (TopCat.of Y)) v = 0 := by rw [hp, ← hq]
  have hfin := one_cup v
  rw [hone, CharClass.cohCast_zero] at hfin
  exact hfin.symm

end KnHemi

end

/-! Audited on every build. -/

#audit_axioms KnHemi.knGen_zeroGenOf

end GroupApproximation.CharClass
