import GroupApproximation.CharClass.LemmaTwoStepCAbsEquiv
import GroupApproximation.CharClass.ThomStepCEuler

/-!
# Step C down to one open hypothesis

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`CharClass/LemmaTwoStepCAbsEquiv.lean` left three open fields on the odd side: the
excision identity `hsu`, the nonvanishing `hg` of the local generator, and the
identification `hgamma` of the top class.  `cc-thom`'s `ThomStepCEuler.lean` collapses the
first two, and this file restates Step C over what is left.

## Why two of the three were free, and why that is a `ZMod 2` fact

The local model is one dimensional, so `hsu_of_ne_zero` and `ne_zero_of_hsu` make

```text
(exc ≪≫ chartIso).hom.hom su = localGenerator r    ⟺    su ≠ 0
```

interchangeable, and `hg` disappears with the abstract `loc`, since the concrete local
generator is known nonzero.  The step that does the work is
`eq_localGenerator_of_ne_zero`, whose kernel is `∀ c : ZMod 2, c ≠ 0 → c = 1`, by
`decide`.  **This is special to mod-2 coefficients.**  Over any other field a nonzero
class is only *some* scalar multiple of the generator, that scalar would survive into the
statement, and the equality form would carry real content that the nonvanishing form does
not.  Worth recording, because "the equality was free" is true here and false in the
obvious generalisation.

`hgamma` is not of that kind: it identifies the top class with the image of the relative
Euler class and stays with `cc-projective`.

## Main results

* `ThomChainEuler` — `ThomChainOpen` with `hsu`, `hg` and the abstract local model gone.
  Its only field that is not `cc-relative`'s green chart data is `hne`.
* `ne_zero_of_thomChainEuler`, `stepC_of_thomChainEuler` — **Step C**, over the
  nonvanishing of the relative Euler class and `hgamma`.

The axiom report is printed at the foot, for the reason given in
`CharClass/LemmaTwoStepCAbsEquiv.lean`: this is hygiene, not foundations, and a line that
prints the answer on every build cannot drift into the wider claim.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open CategoryTheory Limits
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. What is still owed -/

/-- **The chain data with the local model made concrete.**  Compared with
`ThomChainOpen`: `loc` and `locEquiv` are gone, because `chartIso` now lands in
`cc-relative`'s concrete local model; `hg` is gone, because that model's generator is
known nonzero; and `hsu` has become the nonvanishing `hne`.

Every field but `hne` and `hgamma` is `cc-relative`'s and green. -/
structure ThomChainEuler (dd : Fin ℓ → ℕ)
    (gamma : cohomologyZMod2 (lixN dd) (2 * lixRank dd)) where
  /-- The relative group of the pair. -/
  rel : ModuleCat.{0} (ZMod 2)
  /-- The chart group. -/
  chart : ModuleCat.{0} (ZMod 2)
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
  /-- The chart against the concrete local model, fed by `eulerLocalHomeo`
  (`cc-relative`). -/
  chartIso : chart ≅ relCohomology (ZMod 2) (TopCat.of (Fin (lixRank dd) → ℂ))
    (puncturedSet (lixRank dd)) (2 * lixRank dd)
  /-- The relative Euler class. -/
  su : rel
  /-- **Open** (`cc-projective`): the relative Euler class is nonzero.  This is the whole
  of what `hsu` and `hg` together used to say. -/
  hne : su ≠ 0
  /-- **Open** (`cc-projective`): `topClass` is the top Chern class. -/
  hgamma : gamma = j.hom su

/-- `cc-thom`'s conclusion from the shortest bundle. -/
theorem ne_zero_of_thomChainEuler (hdd : ∀ j, 0 < dd j)
    {gamma : cohomologyZMod2 (lixN dd) (2 * lixRank dd)} (D : ThomChainEuler dd gamma) :
    gamma ≠ 0 :=
  topChernClass_ne_zero_of_su_ne_zero_line (puncturedAcyclic_lixZero' hbase_lix hdd)
    D.j D.i D.hexact (nonempty_absEquiv_lix dd hdd) D.exc D.chartIso D.hne D.hgamma

/-! ## 2. Step C -/

/-- **Step C**, over the nonvanishing of the relative Euler class and the identification
of the top class.  Everything else — the base, its punctured acyclicity, its top line,
both sphere models, the excision identity and the local generator — is a theorem. -/
theorem stepC_of_thomChainEuler (chern : LixChernDeg dd) (hdd : ∀ j, 0 < dd j)
    (chain : ∀ (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ) (hGc : Continuous G)
      (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)),
      (∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) →
      ThomChainEuler dd
        (chern (mappingTorus Vmat G circHoriz circHeight)
          (continuous_mappingTorus_lix hGc) (isStarProjection_mappingTorus_lix hGu)
          (lixRank dd))) :
    ∀ G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ, Continuous G →
      (∀ m, IsCornerUnitary (Vmat m) (G m)) →
      (∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) →
      lixTopClass chern (mappingTorus Vmat G circHoriz circHeight) ≠ 0 :=
  stepC_of_chain chern fun G hGc hGu hGe =>
    ne_zero_of_thomChainEuler hdd (chain G hGc hGu hGe)

/-! ## 3. The axiom report

Both print `[propext, Classical.choice, Quot.sound]`.  Kept for the reason in
`CharClass/LemmaTwoStepCAbsEquiv.lean`. -/

#print axioms ne_zero_of_thomChainEuler

#print axioms stepC_of_thomChainEuler

end GroupApproximation.CharClass
