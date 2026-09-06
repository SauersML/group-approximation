import GroupApproximation.CharClass.LemmaTwoStepCEuler

/-!
# Step C in the shape the Thom class will actually arrive in

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`CharClass/LemmaTwoStepCEuler.lean` states Step C over two open fields, `hne` and
`hgamma`, against an abstract relative Euler class `su`.  `cc-thom`'s
`topChernClass_ne_zero_of_su_ne_zero_naturality_line` lets `su` be replaced by the image
of a Thom class `u` under the section, with `hgamma` becoming
`hu : jE.hom u = piStar.hom gamma`.

## This does not reduce the count, and the file says so

**Two fields are open before and two after**: `hgamma` becomes `hu`, and `hne` is
restated about `sRel.hom u`.  `hu` is where the Thom class enters, so it sits behind the
same Leray--Hirsch ladder as everything else, and an audit should count `hu` and `hne`
rather than `hne` alone.

The reason to prefer this shape anyway is that it **matches the object that will discharge
it**.  `cc-projective` will produce a Thom class `u` together with its naturality square,
not an opaque `gamma` with a separate identification, so a structure whose fields are `u`,
`hu` and `hne` can be populated directly, whereas `ThomChainEuler` would need the
identification manufactured after the fact.  `ThomChainEuler` and
`stepC_of_thomChainEuler` remain published for a consumer that has `gamma` first.

## Main results

* `ThomChainThom` — the chain data with the Thom class named.
* `ne_zero_of_thomChainThom`, `stepC_of_thomChainThom` — **Step C**, over `hu` and `hne`.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open CategoryTheory Limits
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The chain data with the Thom class named -/

/-- **Step C's remaining arguments, with `gamma` pinned to a Thom class.**

Compared with `ThomChainEuler`: the relative Euler class is no longer a free `su` but the
image `sRel.hom u` of a Thom class `u`, and the identification `hgamma` is replaced by the
naturality datum `hu`.  The open fields are `hu` and `hne`; everything else is
`cc-relative`'s. -/
structure ThomChainThom (dd : Fin ℓ → ℕ)
    (gamma : cohomologyZMod2 (lixN dd) (2 * lixRank dd)) where
  /-- The relative group of the pair. -/
  rel : ModuleCat.{0} (ZMod 2)
  /-- The chart group. -/
  chart : ModuleCat.{0} (ZMod 2)
  /-- The relative group of the bundle pair, where the Thom class lives. -/
  HrelE : ModuleCat.{0} (ZMod 2)
  /-- The absolute group of the bundle. -/
  HE : ModuleCat.{0} (ZMod 2)
  /-- `j^*`, from the relative group (`cc-relative`). -/
  j : rel ⟶ cohomologyZMod2 (lixN dd) (2 * lixRank dd)
  /-- Restriction to the punctured base (`cc-relative`). -/
  i : cohomologyZMod2 (lixN dd) (2 * lixRank dd) ⟶
    cohomologyZMod2 (TopCat.of ↥({lixZero dd}ᶜ : Set (↥sphereOne × baseM dd)))
      (2 * lixRank dd)
  /-- Exactness at the absolute group (`cc-relative`). -/
  hexact : LinearMap.range j.hom = LinearMap.ker i.hom
  /-- Excision to the chart (`cc-relative`). -/
  exc : rel ≅ chart
  /-- The chart against the concrete local model (`cc-relative`). -/
  chartIso : chart ≅ relCohomology (ZMod 2) (TopCat.of (Fin (lixRank dd) → ℂ))
    (puncturedSet (lixRank dd)) (2 * lixRank dd)
  /-- The bundle pair's own `j^*`. -/
  jE : HrelE ⟶ HE
  /-- The section, relatively. -/
  sRel : HrelE ⟶ rel
  /-- The section, absolutely. -/
  sAbs : HE ⟶ cohomologyZMod2 (lixN dd) (2 * lixRank dd)
  /-- The projection's pullback. -/
  piStar : cohomologyZMod2 (lixN dd) (2 * lixRank dd) ⟶ HE
  /-- The naturality square (`cc-relative`). -/
  hnat : sRel ≫ j = jE ≫ sAbs
  /-- The section splits the projection (`cc-relative`). -/
  hsection : piStar ≫ sAbs = 𝟙 (cohomologyZMod2 (lixN dd) (2 * lixRank dd))
  /-- The Thom class. -/
  u : HrelE
  /-- **Open** (`cc-projective`): `gamma` is the Thom class pulled back.  This is where
  the Thom class enters, so it is behind the Leray--Hirsch ladder. -/
  hu : jE.hom u = piStar.hom gamma
  /-- **Open** (`cc-projective`): the relative Euler class is nonzero. -/
  hne : sRel.hom u ≠ 0

/-- `cc-thom`'s conclusion from the Thom-class bundle. -/
theorem ne_zero_of_thomChainThom (hdd : ∀ j, 0 < dd j)
    {gamma : cohomologyZMod2 (lixN dd) (2 * lixRank dd)} (D : ThomChainThom dd gamma) :
    gamma ≠ 0 :=
  topChernClass_ne_zero_of_su_ne_zero_naturality_line
    (puncturedAcyclic_lixZero' hbase_lix hdd)
    D.j D.i D.hexact (nonempty_absEquiv_lix dd hdd) D.exc D.chartIso
    D.jE D.sRel D.sAbs D.piStar D.hnat D.hsection D.hu D.hne

/-! ## 2. Step C -/

/-- **Step C**, over the Thom class and its nonvanishing.  Two open fields, the same count
as `stepC_of_thomChainEuler`, in the shape `cc-projective` will produce. -/
theorem stepC_of_thomChainThom (chern : LixChernDeg dd) (hdd : ∀ j, 0 < dd j)
    (chain : ∀ (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ) (hGc : Continuous G)
      (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)),
      (∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) →
      ThomChainThom dd
        (chern (mappingTorus Vmat G circHoriz circHeight)
          (continuous_mappingTorus_lix hGc) (isStarProjection_mappingTorus_lix hGu)
          (lixRank dd))) :
    ∀ G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ, Continuous G →
      (∀ m, IsCornerUnitary (Vmat m) (G m)) →
      (∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) →
      lixTopClass chern (mappingTorus Vmat G circHoriz circHeight) ≠ 0 :=
  stepC_of_chain chern fun G hGc hGu hGe =>
    ne_zero_of_thomChainThom hdd (chain G hGc hGu hGe)

/-! ## 3. The axiom report

Both print `[propext, Classical.choice, Quot.sound]`.  Kept for the reason in
`CharClass/LemmaTwoStepCAbsEquiv.lean`. -/

#print axioms ne_zero_of_thomChainThom

#print axioms stepC_of_thomChainThom

end GroupApproximation.CharClass
