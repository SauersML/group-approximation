import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.CharClass.ThomJmNatural
import GroupApproximation.CharClass.ThomCoordinates
import GroupApproximation.CharClass.LIXThomResReduction
import GroupApproximation.CharClass.CohomologyDegreeZero

/-!
# `hres`: the relative Euler class survives the restriction to the ball

Lane `lix-hres` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`LIXThomResReduction` reduced `hres` — the injectivity of `cc-lix-odd`'s `lixRes`
— to the single nonvanishing

```text
(lixRes hGc hGu (2 * lixRank dd)).hom (lixThomClassTerm hGc hGu) ≠ 0,
```

because the source of `lixRes` is a line with `lixThomClassTerm` as its
generator.  This file proves that nonvanishing, and so discharges `hres`.

## The route, and why it is not the ball

The restriction to the ball cannot be computed where it lives.  `thomJmTotal`,
the coordinate map the Thom class is *named* by, exists only over a compact
Hausdorff base, because `bridgeTotal` does; a ball is neither.  So the class is
followed one step further, to the **fibre over the section's zero**, whose base is
a single point and therefore compact, Hausdorff and nonempty for free.

Restricting to the point factors through restricting to the ball, because the
point lies in the ball: `totalInclSub` is the inclusion of one restricted total
space in another, over an inclusion of subsets of the base, and
`relPullback_totalInclOn_sub` says the two restrictions compose to the direct
one.

**The direction matters and is easy to state backwards.**  The factorisation is
used one way only: a class killed by `lixRes` is killed over the point, so
**surviving over the point suffices**.  It is *not* claimed that the two
restrictions have the same kernel, nor that the restriction to the point is
injective, nor that it detects every class; only that it cannot resurrect a class
the ball restriction has already killed.  That one implication is the whole
argument.

Over the point that is a coordinate computation and nothing else.
`ThomJmNatural.thomJmTotal_restrict` says the coordinates restrict coordinatewise,
`ThomCoordinates.thomJmTotal_lixThomClassTerm` says the top coordinate of the Thom
class is `lixTopCoeff dd`, which is the unit of `H^0` of the base, and the unit
restricts to the unit, which is nonzero because a point is nonempty.

**This is not excision**, and the reason is `cc-bundle`'s: excision would need a
set whose closure lies inside the punctured total space, and every such set
contains zero-section points, which the punctured set omits.  Nothing below
excises anything.

**What this does not do.**  It says **nothing about the ball**, which is the
point of the detour: no class is computed there, the relative group over it is
not identified, and no Thom isomorphism over it is used or claimed — there is
none, because `thomJmTotal` needs `bridgeTotal` and `bridgeTotal` needs a compact
Hausdorff base.  `LIXBaseConnected`'s docstring says injectivity becomes the
restriction of `H^0` from the base to the ball "under the Thom isomorphism on
each side"; that describes the mathematics correctly and the available Lean route
not at all, and the difference is exactly why this file exists.  Connectedness of
the base is still used, but through `lixRelLine` and only to make the source rank
one; it does not give the nonvanishing.

It also does not identify `lixRes` with anything, and says nothing about the
other two residues of `lix_topClass_ne_zero_of_thom`, `hsq` and `hclass`.

**No positivity is used.**  There is no `hdd` binder, no projective factor is
peeled, and nothing inducts over the index family, so the empty family `ℓ = 0` —
the tower's own stage 0, where `lixDD 0 : Fin 0 → ℕ` and any `0 < dd j` is
vacuous — is not a special case here.  `lixRank dd = (∑ j, dd j) + 3` is `3`
there, which is all the two landed general-`dd` facts `one_le_lixRank_dd` and
`two_le_two_mul_lixRank` need.

## Main declarations

* `Bundle.totalInclSub` — the inclusion of restricted total spaces, over `W ⊆ U`.
* `relPullback_totalInclOn_sub` — **restricting to `W` factors through `U`.**
* `lixRes_lixThomClassTerm_ne_zero` — **the relative Euler class survives.**
* `injective_lixRes` — **`hres`.**
-/

open CategoryTheory TopologicalSpace
open GroupApproximation.STW59
open GroupApproximation.CharClass.LH
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

set_option linter.unusedSectionVars false

/-! ## 1. Restricting a bundle to a smaller subset of the base -/

namespace Bundle

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

theorem totalInclSub_mem (p : Bundle X ι) {W U : Set X} (h : W ⊆ U)
    (w : Total (p.restrictTo W)) :
    (((⟨((w : ↥W × (ι → ℂ)).1 : X), h (w : ↥W × (ι → ℂ)).1.2⟩ : ↥U),
      (w : ↥W × (ι → ℂ)).2) : ↥U × (ι → ℂ)) ∈ totalSet (p.restrictTo U) :=
  w.2

/-- **The inclusion of one restricted total space in another**, over an inclusion
of subsets of the base.  Only the base point's membership proof changes. -/
def totalInclSub (p : Bundle X ι) {W U : Set X} (h : W ⊆ U) :
    C(Total (p.restrictTo W), Total (p.restrictTo U)) where
  toFun w := ⟨(⟨((w : ↥W × (ι → ℂ)).1 : X), h (w : ↥W × (ι → ℂ)).1.2⟩,
    (w : ↥W × (ι → ℂ)).2), totalInclSub_mem p h w⟩
  continuous_toFun :=
    ((((continuous_subtype_val.comp
      (continuous_fst.comp continuous_subtype_val)).subtype_mk _).prodMk
        (continuous_snd.comp continuous_subtype_val))).subtype_mk _

/-- **The two inclusions compose to the direct one.**  Both forget the base
point's membership entirely; by `rfl` on points. -/
theorem totalInclOn_comp_totalInclSub (p : Bundle X ι) {W U : Set X} (h : W ⊆ U) :
    (totalInclOn p U).comp (totalInclSub p h) = totalInclOn p W :=
  ContinuousMap.ext fun _ => rfl

/-- **It is a map of punctured pairs**, in both directions: the fibre coordinate
is untouched. -/
theorem totalInclSub_mem_puncturedSet_iff (p : Bundle X ι) {W U : Set X} (h : W ⊆ U)
    (w : Total (p.restrictTo W)) :
    ((totalInclSub p h w : Total (p.restrictTo U)) : ↥U × (ι → ℂ))
        ∈ puncturedSet (p.restrictTo U)
      ↔ (w : ↥W × (ι → ℂ)) ∈ puncturedSet (p.restrictTo W) :=
  ⟨fun hw => ⟨w.2, hw.2⟩, fun hw => ⟨totalInclSub_mem p h w, hw.2⟩⟩

end Bundle

section Sub

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

/-- The smaller inclusion, as a map of pairs in the form `relPullback` consumes. -/
theorem totalInclSub_mapsTo (p : Bundle X ι) {W U : Set X} (h : W ⊆ U) :
    ∀ v ∈ ((Subtype.val : Bundle.Total (p.restrictTo W) → ↥W × (ι → ℂ)) ⁻¹'
        Bundle.puncturedSet (p.restrictTo W)),
      (ConcreteCategory.hom (cmap (Bundle.totalInclSub p h))) v
        ∈ ((Subtype.val : Bundle.Total (p.restrictTo U) → ↥U × (ι → ℂ)) ⁻¹'
          Bundle.puncturedSet (p.restrictTo U)) :=
  fun v hv => (Bundle.totalInclSub_mem_puncturedSet_iff p h v).mpr hv

theorem cmap_totalInclSub_comp (p : Bundle X ι) {W U : Set X} (h : W ⊆ U) :
    cmap (Bundle.totalInclSub p h) ≫ cmap (Bundle.totalInclOn p U)
      = cmap (Bundle.totalInclOn p W) := by
  apply TopCat.Hom.ext
  exact ContinuousMap.ext fun _ => rfl

/-- **Restricting the bundle pair to `W` factors through restricting it to `U`.**
This is what lets a nonvanishing detected far down — over a point — be read back
as a nonvanishing over the neighbourhood. -/
theorem relPullback_totalInclOn_sub (p : Bundle X ι) {W U : Set X} (h : W ⊆ U)
    (n : ℕ) :
    relPullback (ZMod 2) (cmap (Bundle.totalInclOn p W)) (totalInclOn_mapsTo p W) n
      = relPullback (ZMod 2) (cmap (Bundle.totalInclOn p U))
          (totalInclOn_mapsTo p U) n
        ≫ relPullback (ZMod 2) (cmap (Bundle.totalInclSub p h))
            (totalInclSub_mapsTo p h) n := by
  rw [← relPullback_comp (ZMod 2) (cmap (Bundle.totalInclSub p h))
    (cmap (Bundle.totalInclOn p U)) (totalInclSub_mapsTo p h) (totalInclOn_mapsTo p U)
    (fun v hv => totalInclOn_mapsTo p U _ (totalInclSub_mapsTo p h v hv)) n]
  exact (relPullback_eq_of_eq (ZMod 2) (cmap_totalInclSub_comp p h) _ n).symm

end Sub

/-! ## 2. The top coefficient survives any restriction -/

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

/-- **The generator of the top coefficient group restricts to a nonzero class.**
It is the unit of degree-zero cohomology, and the unit is nonzero over any
nonempty space. -/
theorem pull_lixTopCoeff_ne_zero {Y : TopCat.{0}} [Nonempty Y] (f : Y ⟶ lixN dd) :
    pull f (2 * lixRank dd - 2 * lixRank dd) (ThomChernDeg.lixTopCoeff dd) ≠ 0 := by
  show pull f (2 * lixRank dd - 2 * lixRank dd)
      (cohCast (show (0 : ℕ) = 2 * lixRank dd - 2 * lixRank dd by omega)
        (one (lixN dd))) ≠ 0
  rw [LH.pull_cohCast, pull_one]
  exact ThomChernDeg.cohCast_ne_zero _ (one_ne_zero_cohZero Y)

/-! ## 3. The nonvanishing, and `hres` -/

set_option maxHeartbeats 1000000 in
/-- **The relative Euler class survives the restriction to the trivialising
ball.**  Equivalently: the Thom class of the mapping-torus bundle pair is not
killed by the restriction to the bundle pair over the neighbourhood of the
section's zero.

The proof follows the class one step further, to the fibre over the zero, where
the base is a point and the Leray–Hirsch coordinates are computable; there the top
coordinate is the unit, which is nonzero. -/
theorem lixRes_lixThomClassTerm_ne_zero (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    (lixRes hGc hGu (2 * lixRank dd)).hom (lixThomClassTerm hGc hGu) ≠ 0 := by
  haveI hnW : Nonempty ↥({lixZero dd} : Set (↥sphereOne × baseM dd)) :=
    ⟨⟨lixZero dd, rfl⟩⟩
  haveI hnW' : Nonempty
      (TopCat.of ↥({lixZero dd} : Set (↥sphereOne × baseM dd))) :=
    ⟨⟨lixZero dd, rfl⟩⟩
  haveI hcW : CompactSpace ↥({lixZero dd} : Set (↥sphereOne × baseM dd)) :=
    isCompact_iff_compactSpace.mp isCompact_singleton
  intro h0
  -- the point lies in the ball
  have hzb : lixZero dd ∈ lixTrivBall hGc hGu := lixZero_mem_lixBaseBall _ _ _
  have hWU : ({lixZero dd} : Set (↥sphereOne × baseM dd)) ⊆ lixTrivBall hGc hGu :=
    Set.singleton_subset_iff.mpr hzb
  -- Leray–Hirsch over the point
  have hrankW : ∀ x : ↥({lixZero dd} : Set (↥sphereOne × baseM dd)),
      (((lixBundle G hGc hGu).restrictTo
        ({lixZero dd} : Set (↥sphereOne × baseM dd))).plusOne).rank x
        = lixRank dd + 1 := fun x => rank_lixBundle_plusOne G hGc hGu _
  have LW : LerayHirschGraded
      (projMapOf (((lixBundle G hGc hGu).restrictTo
        ({lixZero dd} : Set (↥sphereOne × baseM dd))).plusOne))
      (tautEulerOf (((lixBundle G hGc hGu).restrictTo
        ({lixZero dd} : Set (↥sphereOne × baseM dd))).plusOne)) (lixRank dd + 1) :=
    lerayHirschGraded_compact _ (lixRank dd + 1) hrankW
      (Nat.succ_le_succ (Nat.zero_le _))
  -- the coordinates of the restricted class
  have hcoord := thomJmTotal_restrict (lixBundle G hGc hGu)
    ({lixZero dd} : Set (↥sphereOne × baseM dd)) (lixLHplus hGc hGu) LW
    (lixThomClassTerm hGc hGu)
  -- the class is killed over the ball, hence over the point
  have h0' : (relPullback (ZMod 2) (cmap (Bundle.totalInclOn (lixBundle G hGc hGu)
        (lixTrivBall hGc hGu))) (totalInclOn_mapsTo _ _) (2 * lixRank dd)).hom
      (lixThomClassTerm hGc hGu) = 0 := h0
  have hzeroW : (relPullback (ZMod 2) (cmap (Bundle.totalInclOn (lixBundle G hGc hGu)
        ({lixZero dd} : Set (↥sphereOne × baseM dd)))) (totalInclOn_mapsTo _ _)
      (2 * lixRank dd)).hom (lixThomClassTerm hGc hGu) = 0 := by
    rw [relPullback_totalInclOn_sub (lixBundle G hGc hGu) hWU (2 * lixRank dd)]
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
    rw [h0', map_zero]
  -- the top coordinate is the unit, restricted
  have htop : ThomChernDeg.thomJmTotal (lixBundle G hGc hGu) (lixLHplus hGc hGu)
        (lixThomClassTerm hGc hGu) (Fin.last (lixRank dd))
      = ThomChernDeg.lixTopCoeff dd := by
    rw [thomJmTotal_lixThomClassTerm hGc hGu]
    exact ThomDeg.thomLift_last _ _
  have hfin := congrFun hcoord (Fin.last (lixRank dd))
  simp only [hzeroW, map_zero, Pi.zero_apply, htop] at hfin
  exact pull_lixTopCoeff_ne_zero
    (inclSubtype ({lixZero dd} : Set (↥sphereOne × baseM dd))) hfin.symm

/-- **`hres`.**  The injectivity `lix_topClass_ne_zero_of_thom` takes, with no
hypothesis beyond `hGc` and `hGu`. -/
theorem injective_lixRes (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    Function.Injective (lixRes hGc hGu (2 * lixRank dd)).hom :=
  ThomChernDeg.injective_lixRes_of_ne_zero hGc hGu
    (lixRes_lixThomClassTerm_ne_zero hGc hGu)

/-! Audited on every build: `#audit_axioms` prints the axiom closure and
**fails the build** if it leaves the classical allowlist, which `#print axioms`
does not. -/

#audit_axioms injective_lixRes

end

end GroupApproximation.CharClass
