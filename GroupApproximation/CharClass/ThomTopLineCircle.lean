import GroupApproximation.CharClass.ThomTopLine
import GroupApproximation.CharClass.CohomologyKunnethZero

/-!
# The circle step of the top-line induction

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C, hypothesis 8).

`ThomTopLine.lean` reduces the top line of `N = S¹ × S⁵ × ∏ⱼ ℂP^{dⱼ}` to the one
case its Mayer–Vietoris argument cannot reach, `CircleTopLineStep`: crossing with
`S¹` raises the top degree by one.  It is the bottom of both inductions because
the two arcs covering `S¹` meet in a **disconnected** set, so the connecting map
is no longer an isomorphism and its kernel has to be computed.

This file computes it, and so discharges the hypothesis.

## The computation

Cover `A × S¹` by the two hemispherical pieces of `cc-cohom-api`'s `KnHemi`, whose
intersection is `A × S⁰`.  Since `A` has no cohomology above `p`, the connecting
map

```text
δ : H^p(A × S⁰; F₂) → H^{p+1}(A × S¹; F₂)
```

is **surjective**, and exactness identifies its kernel as the set of sums of
restrictions from the two pieces.  Both pieces are `A` *through the projection*
(`KnHemi.exists_pull_prSub_hemiU`, `KnHemi.mvResWU_pull_prSub`), so that kernel is
exactly the image of `pr_A^*`.  Counting over `F₂`:

| space | dimension |
| --- | --- |
| `H^p(A × S⁰; F₂)` | `2` |
| `ker δ = range pr_A^*` | `1` |
| `H^{p+1}(A × S¹; F₂)` | `1` |

The two dimension inputs are the disjoint splitting of `S⁰` (`mvPairEquiv`, whose
pieces are contractible) and the fact that a slice retracts the projection
(`pull_knPrY_injective`).  No cup product and no cross product is used.

## Main declarations

* `sphereZeroProdEquiv` — `H^k(A × S⁰; F₂) ≅ H^k(A; F₂)²`.
* `ker_mvDelta_circle` — the kernel of the connecting map is the image of `pr_A^*`.
* `hasTopLine_prod_circle` — the circle step.
* `circleTopLineStep` — **the hypothesis of `ThomTopLine.lean`, discharged.**
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

variable (A : Type) [TopologicalSpace A] (p : ℕ)

/-! ## 1. `A × S⁰` splits into two copies of `A` -/

/-- The positive half of `A × S⁰`, typed over the `TopCat` object so that the
ambient space of `mvResU` and friends is inferable. -/
abbrev szPosProd : Opens ↥(TopCat.of (A × Sphere 0)) := prodOpen A sphereZeroPos

/-- The negative half of `A × S⁰`. -/
abbrev szNegProd : Opens ↥(TopCat.of (A × Sphere 0)) := prodOpen A sphereZeroNeg

theorem szProd_sup : szPosProd A ⊔ szNegProd A = ⊤ := prodOpen_sup A sphereZero_sup

instance isEmpty_szProd_inter :
    IsEmpty ↥(((szPosProd A : Set ↥(TopCat.of (A × Sphere 0))))
      ∩ ((szNegProd A : Set ↥(TopCat.of (A × Sphere 0))))) := by
  refine Set.isEmpty_coe_sort.2 (Set.eq_empty_iff_forall_notMem.2 ?_)
  rintro q ⟨h1, h2⟩
  have hq : q.2 ∈ ((sphereZeroPos : Set (Sphere 0)) ∩ (sphereZeroNeg : Set (Sphere 0))) :=
    ⟨h1, h2⟩
  rw [sphereZero_inter_empty] at hq
  exact hq

/-- The positive half of `A × S⁰` has the cohomology of `A`. -/
def szPosProdCoh (k : ℕ) :
    Hmod2 (TopCat.of A) k ≃ₗ[ZMod 2] Hmod2 (mvU (szPosProd A)) k :=
  (cohProdContractible A ↥((sphereZeroPos : Opens (Sphere 0)) : Set (Sphere 0)) k).trans
    (prodOpenCohEquiv A sphereZeroPos k)

/-- The negative half of `A × S⁰` has the cohomology of `A`. -/
def szNegProdCoh (k : ℕ) :
    Hmod2 (TopCat.of A) k ≃ₗ[ZMod 2] Hmod2 (mvU (szNegProd A)) k :=
  (cohProdContractible A ↥((sphereZeroNeg : Opens (Sphere 0)) : Set (Sphere 0)) k).trans
    (prodOpenCohEquiv A sphereZeroNeg k)

/-- **`H^k(A × S⁰; F₂) ≅ H^k(A; F₂)²`.**  The two halves of `S⁰` are disjoint, so
the cohomology splits, and each half is contractible. -/
def sphereZeroProdEquiv (k : ℕ) :
    Hmod2 (TopCat.of (A × Sphere 0)) k
      ≃ₗ[ZMod 2] (Hmod2 (TopCat.of A) k × Hmod2 (TopCat.of A) k) :=
  (mvPairEquiv (szPosProd A) (szNegProd A) (szProd_sup A) k).trans
    ((szPosProdCoh A k).symm.prodCongr (szNegProdCoh A k).symm)

/-- `H^p(A × S⁰; F₂)` is two dimensional when `A` has a top line in degree `p`. -/
theorem finrank_prod_sphereZero (hA : HasTopLine A p) :
    Module.finrank (ZMod 2) (Hmod2 (TopCat.of (A × Sphere 0)) p) = 2 := by
  obtain ⟨l⟩ := hA.line
  rw [(sphereZeroProdEquiv A p).finrank_eq, (l.prodCongr l).finrank_eq,
    Module.finrank_prod, Module.finrank_self]

/-- The band of `A × S¹` is `A × S⁰`, so it too is two dimensional. -/
theorem finrank_band_circle (hA : HasTopLine A p) :
    Module.finrank (ZMod 2) (Hmod2 (TopCat.of ↥(KnHemi.bandSet A 0)) p) = 2 := by
  rw [← (KnHemi.bandPullEquiv A 0 p).finrank_eq]
  exact finrank_prod_sphereZero A p hA

/-! ## 2. The projection pullback is injective -/

/-- **A slice retracts the projection**, so pulling back from `A` to the band of
`A × S¹` is injective. -/
theorem pullLinear_prSub_band_injective (k : ℕ) :
    Function.Injective (pullLinear (KnHemi.prSub A 0 (KnHemi.bandSet A 0)) k) := by
  obtain ⟨s⟩ := nonempty_sphereZeroPos
  intro u u' h
  have h2 : pull (cmap (KnHemi.bandHomotopyEquiv A 0).toFun) k (pull (knPrY A 0) k u)
      = pull (cmap (KnHemi.bandHomotopyEquiv A 0).toFun) k (pull (knPrY A 0) k u') := by
    rw [KnHemi.pull_bandHE_knPrY, KnHemi.pull_bandHE_knPrY]
    exact h
  exact pull_knPrY_injective A 0 (s : Sphere 0) k (KnHemi.pull_bandHE_injective A 0 k h2)

/-! ## 3. The kernel of the connecting map -/

set_option maxHeartbeats 1000000 in
/-- **The kernel of the connecting map is exactly the image of `pr_A^*`.**  One
inclusion is exactness plus the fact that both hemispherical pieces are `A`
through the projection; the other is the same computation of `mvResWU` run
forwards, with the second piece contributing nothing. -/
theorem ker_mvDelta_circle :
    LinearMap.ker (mvDelta (KnHemi.hemiU A 0) (KnHemi.hemiV A 0) (KnHemi.hemi_sup A 0) p).hom
      = LinearMap.range (pullLinear (KnHemi.prSub A 0 (KnHemi.bandSet A 0)) p) := by
  apply le_antisymm
  · intro w hw
    rw [LinearMap.mem_ker] at hw
    obtain ⟨a, b, hab⟩ :=
      (mvExactW (KnHemi.hemiU A 0) (KnHemi.hemiV A 0) (KnHemi.hemi_sup A 0) p w).1 hw
    obtain ⟨c, hc⟩ := KnHemi.exists_pull_prSub_of_res A 0 p w a b hab
    exact ⟨c, hc⟩
  · rintro w ⟨c, rfl⟩
    rw [LinearMap.mem_ker]
    refine (mvExactW (KnHemi.hemiU A 0) (KnHemi.hemiV A 0) (KnHemi.hemi_sup A 0) p _).2
      ⟨pull (KnHemi.prSub A 0 (KnHemi.hemiUSet A 0)) p c, 0, ?_⟩
    show (mvResWU (KnHemi.hemiU A 0) (KnHemi.hemiV A 0) (KnHemi.hemi_sup A 0) p).hom
          (pull (KnHemi.prSub A 0 (KnHemi.hemiUSet A 0)) p c)
        + (mvResWV (KnHemi.hemiU A 0) (KnHemi.hemiV A 0) (KnHemi.hemi_sup A 0) p).hom 0
        = pull (KnHemi.prSub A 0 (KnHemi.bandSet A 0)) p c
    rw [KnHemi.mvResWU_pull_prSub, map_zero, add_zero]

/-! ## 4. The circle step -/

set_option maxHeartbeats 1000000 in
/-- **The circle step.**  If the mod-2 cohomology of `A` is a line in its top
degree `p`, then that of `A × S¹` is a line in degree `p + 1`. -/
theorem hasTopLine_prod_circle (hA : HasTopLine A p) : HasTopLine (A × Sphere 1) (p + 1) := by
  have hUz : IsZero (Hmod2 (mvU (KnHemi.hemiU A 0)) (p + 1)) :=
    isZero_prodOpen_of_contractible A (upperOpens 0) (p + 1) (hA.vanish (p + 1) (by omega))
  have hVz : IsZero (Hmod2 (mvU (KnHemi.hemiV A 0)) (p + 1)) :=
    isZero_prodOpen_of_contractible A (lowerOpens 0) (p + 1) (hA.vanish (p + 1) (by omega))
  haveI := ModuleCat.subsingleton_of_isZero hUz
  haveI := ModuleCat.subsingleton_of_isZero hVz
  have hsurj : Function.Surjective
      (mvDelta (KnHemi.hemiU A 0) (KnHemi.hemiV A 0) (KnHemi.hemi_sup A 0) p).hom := by
    intro x
    exact (mvExactX (KnHemi.hemiU A 0) (KnHemi.hemiV A 0) (KnHemi.hemi_sup A 0) p x).1
      ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  haveI : Module.Finite (ZMod 2) (Hmod2 (TopCat.of ↥(KnHemi.bandSet A 0)) p) :=
    Module.finite_of_finrank_pos (by rw [finrank_band_circle A p hA]; omega)
  have hrn := LinearMap.finrank_range_add_finrank_ker
    (mvDelta (KnHemi.hemiU A 0) (KnHemi.hemiV A 0) (KnHemi.hemi_sup A 0) p).hom
  have hkerrank : Module.finrank (ZMod 2)
      (LinearMap.ker (mvDelta (KnHemi.hemiU A 0) (KnHemi.hemiV A 0)
        (KnHemi.hemi_sup A 0) p).hom) = 1 := by
    obtain ⟨l⟩ := hA.line
    rw [ker_mvDelta_circle A p,
      LinearMap.finrank_range_of_inj (pullLinear_prSub_band_injective A p), l.finrank_eq,
      Module.finrank_self]
  have hrangerank : Module.finrank (ZMod 2)
      (LinearMap.range (mvDelta (KnHemi.hemiU A 0) (KnHemi.hemiV A 0)
        (KnHemi.hemi_sup A 0) p).hom)
      = Module.finrank (ZMod 2) (Hmod2 (TopCat.of (A × Sphere 1)) (p + 1)) :=
    (LinearEquiv.ofTop _ (LinearMap.range_eq_top.2 hsurj)).finrank_eq
  have hfin : Module.finrank (ZMod 2) (Hmod2 (TopCat.of (A × Sphere 1)) (p + 1)) = 1 := by
    rw [hkerrank, finrank_band_circle A p hA, hrangerank] at hrn
    omega
  haveI : Module.Finite (ZMod 2) (Hmod2 (TopCat.of (A × Sphere 1)) (p + 1)) :=
    Module.finite_of_finrank_pos (by rw [hfin]; omega)
  refine ⟨fun k hk => (kunnethFactor_sphere 1).prod A p hA.vanish k (by omega), ⟨?_⟩⟩
  exact LinearEquiv.ofFinrankEq _ _ (by rw [hfin, Module.finrank_self])

/-- **The hypothesis of `ThomTopLine.lean`, discharged.** -/
theorem circleTopLineStep : CircleTopLineStep := by
  intro A _ p hA
  exact hasTopLine_prod_circle A p hA

end

end GroupApproximation.CharClass
