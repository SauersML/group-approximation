import GroupApproximation.CharClass.CohomologyKunnethStep
import GroupApproximation.CharClass.CohomologySphereZero
import GroupApproximation.CharClass.MayerVietorisDisjoint

/-!
# The base of the Künneth induction: the zero sphere

`S⁰` is two points, and the two open halves are disjoint, so cohomology splits
(`mvPairEquiv`).  The class `zeroGen` is the one that restricts to `1` on the
positive point and to `0` on the negative one.

`KnGen 0 zeroGen` is the stronger form of the injectivity statement, the one that
allows a pullback from the base on the right.  It has to be, because in degree
zero a slice does not kill a class pulled back from the sphere factor.  What
replaces that is the two-point structure: the two slices give the same class `c`
on the base, and the two restrictions of `zeroGen` add up to `1`, so subtracting
the two equations leaves `1 ⌣ v = 0`.

## Main declarations

* `KnHemi.zeroGen`, `KnHemi.mvResU_zeroGen`, `KnHemi.mvResV_zeroGen`.
* `KnHemi.knGen_zeroGen` — the base case.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace KnHemi

/-! ## 1. The two halves as opens of the `TopCat` object -/

/-- The positive half of `S⁰`, typed over the `TopCat` object so that the ambient
space of `mvResU` and friends is inferable. -/
abbrev szPos : Opens ↥(TopCat.of (Sphere 0)) := sphereZeroPos

/-- The negative half of `S⁰`. -/
abbrev szNeg : Opens ↥(TopCat.of (Sphere 0)) := sphereZeroNeg

theorem sz_sup : szPos ⊔ szNeg = ⊤ := sphereZero_sup

instance isEmpty_sz_inter :
    IsEmpty ↥((szPos : Set ↥(TopCat.of (Sphere 0)))
      ∩ (szNeg : Set ↥(TopCat.of (Sphere 0)))) :=
  Set.isEmpty_coe_sort.2 sphereZero_inter_empty

/-! ## 2. The generator -/

/-- The class of `H^0(S⁰; F₂)` that is `1` on the positive point and `0` on the
negative one. -/
def zeroGen : Hmod2 (TopCat.of (Sphere 0)) 0 :=
  (mvPairEquiv szPos szNeg sz_sup 0).symm (one (mvU szPos), 0)

theorem mvPair_zeroGen :
    ((mvResU szPos szNeg sz_sup 0).hom zeroGen,
      (mvResV szPos szNeg sz_sup 0).hom zeroGen) = (one (mvU szPos), 0) :=
  (mvPairEquiv szPos szNeg sz_sup 0).apply_symm_apply _

theorem mvResU_zeroGen :
    (mvResU szPos szNeg sz_sup 0).hom zeroGen = one (mvU szPos) :=
  congrArg Prod.fst mvPair_zeroGen

theorem mvResV_zeroGen : (mvResV szPos szNeg sz_sup 0).hom zeroGen = 0 :=
  congrArg Prod.snd mvPair_zeroGen

/-! ## 3. The two point evaluations -/

theorem pull_const_zeroGen_pos (Y : Type) [TopologicalSpace Y]
    (p : ↥(szPos : Set ↥(TopCat.of (Sphere 0)))) :
    pull (cmap (ContinuousMap.const Y (p : Sphere 0))) 0 zeroGen = one (TopCat.of Y) := by
  have hres : pull (sInclusion (szPos : Set ↥(TopCat.of (Sphere 0)))) 0 zeroGen
      = one (mvU szPos) := by
    rw [← cohPullback_apply_eq, ← mvResU_eq_pull]
    exact mvResU_zeroGen
  have hfac : (cmap (ContinuousMap.const Y (p : Sphere 0))
      : TopCat.of Y ⟶ TopCat.of (Sphere 0))
      = cmap (ContinuousMap.const Y p)
        ≫ sInclusion (szPos : Set ↥(TopCat.of (Sphere 0))) := rfl
  rw [hfac, pull_comp, hres, pull_one]

theorem pull_const_zeroGen_neg (Y : Type) [TopologicalSpace Y]
    (q : ↥(szNeg : Set ↥(TopCat.of (Sphere 0)))) :
    pull (cmap (ContinuousMap.const Y (q : Sphere 0))) 0 zeroGen = 0 := by
  have hres : pull (sInclusion (szNeg : Set ↥(TopCat.of (Sphere 0)))) 0 zeroGen = 0 := by
    rw [← cohPullback_apply_eq, ← mvResV_eq_pull]
    exact mvResV_zeroGen
  have hfac : (cmap (ContinuousMap.const Y (q : Sphere 0))
      : TopCat.of Y ⟶ TopCat.of (Sphere 0))
      = cmap (ContinuousMap.const Y q)
        ≫ sInclusion (szNeg : Set ↥(TopCat.of (Sphere 0))) := rfl
  rw [hfac, pull_comp, hres, pull_zero]

/-! ## 4. The base case -/

set_option maxHeartbeats 1000000 in
/-- **The base of the Künneth induction.** -/
theorem knGen_zeroGen : KnGen 0 zeroGen := by
  intro Y _ m v c hc
  obtain ⟨p⟩ := nonempty_sphereZeroPos
  obtain ⟨q⟩ := nonempty_sphereZeroNeg
  have hp := congrArg (pull (knSlice Y 0 (p : Sphere 0)) (0 + m)) hc
  rw [pull_cup, pull_knSlice_knPrY, pull_knSlice_knPrY, pull_knSlice_knPrS_const,
    pull_const_zeroGen_pos] at hp
  have hq := congrArg (pull (knSlice Y 0 (q : Sphere 0)) (0 + m)) hc
  rw [pull_cup, pull_knSlice_knPrY, pull_knSlice_knPrY, pull_knSlice_knPrS_const,
    pull_const_zeroGen_neg, zero_cup] at hq
  have hone : cup (one (TopCat.of Y)) v = 0 := by rw [hp, ← hq]
  have hfin := one_cup v
  rw [hone, cohCast_zero] at hfin
  exact hfin.symm

end KnHemi

end

end GroupApproximation.CharClass
