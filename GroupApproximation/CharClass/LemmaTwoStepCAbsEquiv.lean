import GroupApproximation.CharClass.LIXStepESpheresDischarged
import GroupApproximation.CharClass.ThomTopLineLIX

/-!
# Step C with the top line discharged too

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`cc-thom`'s `ThomTopLineLIX.lean` proves that the top mod-2 cohomology of the LIX base

```text
N = S¹ × S⁵ × ∏ⱼ ℂP^{dⱼ}
```

is one-dimensional, by a Mayer--Vietoris induction over the same re-nesting this lane
built for `puncturedAcyclic_lixBase`.  It leaves one input open: a homeomorphism from
this lane's Hermitian five-sphere `STW59.unitVectors (Fin 3)` to the vendored model
`Sphere 5`, which is the very object `CharClass/LIXStepESphereModel.lean` already
supplies.  Supplying it here closes the `absEquiv` field of `ThomChainData`.

## The one mismatch, and why choice appears

`HasTopLine.line` concludes a `Nonempty` of the linear equivalence, while
`ThomChainData.absEquiv` is a *data* field.  So the bridge is `Nonempty.some`, and this
is the only place in the lane where `Classical.choice` is used.  That is harmless: the
field is used only through `topChernClass_ne_zero_of_chain`, whose conclusion is a `Prop`.

## What is left after this file

Of `cc-thom`'s ten chain arguments, `hacyclic` was discharged in
`CharClass/LIXStepESpheresDischarged.lean` and `absEquiv` is discharged here.  The three
that remain — `hsu`, `hg` and `hgamma` — all need the Thom class and sit with
`cc-projective` and `cc-relative`.  `ThomChainOpen` below is `ThomChainData` with the
`absEquiv` field removed, so its field list is exactly what is still owed.

## Main results

* `unitVectorsThreeHomeoSphere` — this lane's homeomorphism, at `cc-thom`'s type.
* `absEquivLix` — **the top line at `N`**, unconditional in `dd` beyond positivity.
* `ThomChainOpen`, `ThomChainOpen.toThomChainData` — the remaining arguments.
* `stepC_of_thomChainOpen` — **Step C**, over the three open fields and the green ones.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open CategoryTheory Limits
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The model homeomorphism, at the vendored type -/

/-- **This lane's five-sphere is the vendored `Sphere 5`.**  `Sphere n` is a reducible
abbreviation for `↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1)`, which at `n = 5`
is the target of `unitVectorsThreeHomeo` on the nose, so there is nothing to prove. -/
def unitVectorsThreeHomeoSphere : ↥(unitVectors (Fin 3)) ≃ₜ Sphere 5 :=
  unitVectorsThreeHomeo

/-! ## 2. The top line at `N` -/

/-- **`H^{2r}(N; F₂)` is a line**, with the model transport discharged; `cc-thom`'s
`absEquiv_lixN` fed this lane's homeomorphism. -/
theorem nonempty_absEquiv_lix (dd : Fin ℓ → ℕ) (hdd : ∀ j, 0 < dd j) :
    Nonempty (cohomologyZMod2 (lixN dd) (2 * lixRank dd) ≃ₗ[ZMod 2] ZMod 2) :=
  absEquiv_lixN unitVectorsThreeHomeoSphere dd hdd

/-- The linear equivalence itself, chosen. -/
def absEquivLix (dd : Fin ℓ → ℕ) (hdd : ∀ j, 0 < dd j) :
    cohomologyZMod2 (lixN dd) (2 * lixRank dd) ≃ₗ[ZMod 2] ZMod 2 :=
  (nonempty_absEquiv_lix dd hdd).some

/-! ## 3. What is still owed -/

/-- **`ThomChainData` with `absEquiv` removed.**  Every field here is either green in
`cc-relative` (`j`, `i`, `hexact`, `exc`, `chartIso`, `locEquiv`) or one of the three open
Thom-class obligations (`hsu`, `hg`, `hgamma`). -/
structure ThomChainOpen (dd : Fin ℓ → ℕ)
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

/-- The top line is supplied, so the shorter bundle gives the longer one. -/
def ThomChainOpen.toThomChainData (hdd : ∀ j, 0 < dd j)
    {gamma : cohomologyZMod2 (lixN dd) (2 * lixRank dd)} (D : ThomChainOpen dd gamma) :
    ThomChainData dd gamma where
  rel := D.rel
  chart := D.chart
  loc := D.loc
  j := D.j
  i := D.i
  hexact := D.hexact
  absEquiv := absEquivLix dd hdd
  exc := D.exc
  chartIso := D.chartIso
  locEquiv := D.locEquiv
  su := D.su
  g := D.g
  hsu := D.hsu
  hg := D.hg
  hgamma := D.hgamma

/-- `cc-thom`'s conclusion from the shorter bundle: both `hacyclic` and `absEquiv` are
now theorems of this lane. -/
theorem ne_zero_of_thomChainOpen (hdd : ∀ j, 0 < dd j)
    {gamma : cohomologyZMod2 (lixN dd) (2 * lixRank dd)} (D : ThomChainOpen dd gamma) :
    gamma ≠ 0 :=
  ne_zero_of_thomChain (puncturedAcyclic_lixZero' hbase_lix hdd) (D.toThomChainData hdd)

/-! ## 4. Step C -/

/-- **Step C**, over the three open Thom-class fields and `cc-relative`'s green ones.
Nothing about the base, its punctured acyclicity, its top line or the two sphere models is
assumed any more. -/
theorem stepC_of_thomChainOpen (chern : LixChernDeg dd) (hdd : ∀ j, 0 < dd j)
    (chain : ∀ (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ) (hGc : Continuous G)
      (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)),
      (∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) →
      ThomChainOpen dd
        (chern (mappingTorus Vmat G circHoriz circHeight)
          (continuous_mappingTorus_lix hGc) (isStarProjection_mappingTorus_lix hGu)
          (lixRank dd))) :
    ∀ G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ, Continuous G →
      (∀ m, IsCornerUnitary (Vmat m) (G m)) →
      (∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) →
      lixTopClass chern (mappingTorus Vmat G circHoriz circHeight) ≠ 0 :=
  stepC_of_chain chern fun G hGc hGu hGe =>
    ne_zero_of_thomChainOpen hdd (chain G hGc hGu hGe)

end GroupApproximation.CharClass
