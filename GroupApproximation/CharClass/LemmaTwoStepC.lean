import GroupApproximation.CharClass.LemmaTwoTopClass
import GroupApproximation.CharClass.LIXStepEBase
import GroupApproximation.CharClass.EulerLocalAssembly

/-!
# Step C at the real objects: the odd side wired to `cc-thom`

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`CharClass/LemmaTwoTopClass.lean`'s `stepC_of_chain` takes `cc-thom`'s *conclusion* as one
hypothesis.  This file takes their *argument list* instead, so that each remaining
obligation is named and owned separately, and so that the one argument this lane owns —
the punctured acyclicity — is actually discharged rather than assumed.

`ThomChainData` mirrors the arguments of `topChernClass_ne_zero_of_chain` other than
`hacyclic`.  Of its fields, `j`, `i`, `hexact`, `exc`, `chartIso` and `locEquiv` are
`cc-relative`'s and green; `absEquiv` `cc-thom` is attempting; and `hsu`, `hg` and `hgamma`
are the three genuinely open ones, all behind `cc-projective`'s Leray--Hirsch ladder
because all three need the Thom class.

## The degree

`cc-thom` asked for the degree index in added form, so `lixTopDegree dd = 2 ∑ⱼ dⱼ + 6`,
while the Chern assignment of `LemmaTwoTopClass` is indexed by the rank and lands in
degree `2 * lixRank dd`.  Those are equal but not definitionally, so this file works at
`2 * lixRank dd` throughout and converts once, in `puncturedAcyclic_lixZero`.

## Main results

* `lixZero` — the section's single zero, as a point of `N`.
* `puncturedAcyclic_lixZero` — `hacyclic` at that point, discharged from this lane's own
  `puncturedAcyclic_lixBase`.
* `ThomChainData`, `ne_zero_of_thomChain` — `cc-thom`'s remaining arguments, bundled.
* `stepC_of_thomChain` — **Step C**, with `hacyclic` gone.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open CategoryTheory Limits
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The zero, and the punctured acyclicity there -/

/-- The single zero of the manuscript's section, as a point of `N`. -/
def lixZero (dd : Fin ℓ → ℕ) : ↥sphereOne × baseM dd := (southPole, lixZeroPoint dd)

/-- **`hacyclic`, discharged.**  `puncturedAcyclic_lixBase` at the zero, converted from the
added degree form to the rank form. -/
theorem puncturedAcyclic_lixZero
    (hCPacyclic : ∀ d : ℕ, 0 < d → ∀ w : CP d, PuncturedAcyclic (CP d) (2 * d) w)
    (kCP : ∀ d : ℕ, 0 < d → KunnethFactor (CP d) (2 * d))
    (kCPpunct : ∀ d : ℕ, 0 < d → ∀ w : CP d,
      KunnethFactor ↥({w}ᶜ : Set (CP d)) (2 * d - 1))
    (hbase : ∀ w : ↥sphereOne × ↥(unitVectors (Fin 3)),
      PuncturedAcyclic (↥sphereOne × ↥(unitVectors (Fin 3))) 6 w)
    (hdd : ∀ j, 0 < dd j) :
    PuncturedAcyclic (↥sphereOne × baseM dd) (2 * lixRank dd) (lixZero dd) := by
  have h := puncturedAcyclic_lixBase_lixTopDegree hCPacyclic kCP kCPpunct hbase dd hdd
    (lixZero dd)
  rwa [lixTopDegree_eq_two_mul_lixRank] at h

/-! ## 2. `cc-thom`'s remaining arguments -/

/-- **The arguments of `topChernClass_ne_zero_of_chain` other than `hacyclic`**, for one
class `gamma` on the LIX base.

Owners: `j`, `i`, `hexact`, `exc`, `chartIso`, `locEquiv` are `cc-relative`'s and green;
`absEquiv` is `cc-thom`'s and in progress; `hsu`, `hg` and `hgamma` are the three open
ones, all behind `cc-projective`'s Leray--Hirsch ladder. -/
structure ThomChainData (dd : Fin ℓ → ℕ)
    (gamma : cohomologyZMod2 (lixN dd) (2 * lixRank dd)) where
  /-- The relative group of the pair. -/
  rel : ModuleCat.{0} (ZMod 2)
  /-- The chart group. -/
  chart : ModuleCat.{0} (ZMod 2)
  /-- The local model's group. -/
  loc : ModuleCat.{0} (ZMod 2)
  /-- `j^*`, from the relative group (`cc-relative`). -/
  j : rel ⟶ cohomologyZMod2 (lixN dd) (2 * lixRank dd)
  /-- Restriction to the punctured base (`cc-relative`). -/
  i : cohomologyZMod2 (lixN dd) (2 * lixRank dd) ⟶
    cohomologyZMod2 (TopCat.of ↥({lixZero dd}ᶜ : Set (↥sphereOne × baseM dd)))
      (2 * lixRank dd)
  /-- Exactness at the absolute group (`cc-relative`). -/
  hexact : LinearMap.range j.hom = LinearMap.ker i.hom
  /-- The top class of the base is a line (`cc-thom`). -/
  absEquiv : cohomologyZMod2 (lixN dd) (2 * lixRank dd) ≃ₗ[ZMod 2] ZMod 2
  /-- Excision to the chart (`cc-relative`). -/
  exc : rel ≅ chart
  /-- The chart is a homeomorphism of pairs, fed by `eulerLocalHomeo` (`cc-relative`). -/
  chartIso : chart ≅ loc
  /-- The local model is a line (`cc-relative`). -/
  locEquiv : loc ≃ₗ[ZMod 2] ZMod 2
  /-- The relative Euler class. -/
  su : rel
  /-- Its image in the local model. -/
  g : loc
  /-- **Open** (`cc-projective`): the relative Euler class excises to the local generator. -/
  hsu : (exc ≪≫ chartIso).hom.hom su = g
  /-- **Open** (`cc-relative`'s `localGenerator_ne_zero`, once `u` exists). -/
  hg : g ≠ 0
  /-- **Open** (`cc-projective`): `topClass` is the top Chern class. -/
  hgamma : gamma = j.hom su

/-- `cc-thom`'s conclusion, from the bundle plus this lane's `hacyclic`. -/
theorem ne_zero_of_thomChain
    (hacyclic : PuncturedAcyclic (↥sphereOne × baseM dd) (2 * lixRank dd) (lixZero dd))
    {gamma : cohomologyZMod2 (lixN dd) (2 * lixRank dd)} (D : ThomChainData dd gamma) :
    gamma ≠ 0 :=
  topChernClass_ne_zero_of_chain hacyclic D.j D.i D.hexact D.absEquiv D.exc D.chartIso
    D.locEquiv D.hsu D.hg D.hgamma

/-! ## 3. Step C, with `hacyclic` gone -/

/-- **Step C.**  The punctured acyclicity is discharged from this lane's own
`puncturedAcyclic_lixBase`; what remains per mapping torus is `cc-thom`'s bundle, whose
open fields are three. -/
theorem stepC_of_thomChain (chern : LixChernDeg dd)
    (hCPacyclic : ∀ d : ℕ, 0 < d → ∀ w : CP d, PuncturedAcyclic (CP d) (2 * d) w)
    (kCP : ∀ d : ℕ, 0 < d → KunnethFactor (CP d) (2 * d))
    (kCPpunct : ∀ d : ℕ, 0 < d → ∀ w : CP d,
      KunnethFactor ↥({w}ᶜ : Set (CP d)) (2 * d - 1))
    (hbase : ∀ w : ↥sphereOne × ↥(unitVectors (Fin 3)),
      PuncturedAcyclic (↥sphereOne × ↥(unitVectors (Fin 3))) 6 w)
    (hdd : ∀ j, 0 < dd j)
    (chain : ∀ (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ) (hGc : Continuous G)
      (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)),
      (∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) →
      ThomChainData dd
        (chern (mappingTorus Vmat G circHoriz circHeight)
          (continuous_mappingTorus_lix hGc) (isStarProjection_mappingTorus_lix hGu)
          (lixRank dd))) :
    ∀ G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ, Continuous G →
      (∀ m, IsCornerUnitary (Vmat m) (G m)) →
      (∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) →
      lixTopClass chern (mappingTorus Vmat G circHoriz circHeight) ≠ 0 :=
  stepC_of_chain chern fun G hGc hGu hGe =>
    ne_zero_of_thomChain
      (puncturedAcyclic_lixZero hCPacyclic kCP kCPpunct hbase hdd)
      (chain G hGc hGu hGe)

end GroupApproximation.CharClass
