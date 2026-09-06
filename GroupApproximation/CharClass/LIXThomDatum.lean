import GroupApproximation.CharClass.LIXBundlePair
import GroupApproximation.CharClass.ThomStepCOddIso

/-!
# The Thom-class datum at the mapping-torus bundle

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`ThomStepCOddIso.topChernClass_ne_zero_odd_iso` takes a class `u` of the relative
group of the bundle pair together with `hu : u ≠ 0`.  This file produces that
datum at `cc-lix-odd`'s concrete objects, so their `ThomChainData` closes the
moment the ring side lands.

The relative group is `relCohomology (ZMod 2) (lixTotalPair …) (lixPuncturedInTotal …) n`,
which is the source of their `lixSRel`, so the `u` built here is exactly the one
their `sRel` consumes.

## What is a hypothesis, and why

Two things, both named rather than assumed silently.

* **The Leray–Hirsch instance**, in the shape `cc-projective`'s
  `lerayHirschGraded_of_trivializing_cover` publishes: `LerayHirschGraded f ξ r`
  for the projectivised bundle.  When their instance lands this discharges by one
  application.
* **The degreewise identification** of the relative group with the Leray–Hirsch
  coefficient groups — the `ThomDeg` data.  This is *not* the same as the
  previous item and is the bridge between them: `LerayHirschGraded` is indexed by
  `lhDomainCard r n`, which equals `r` at the top degree but not definitionally,
  so producing the `ThomDeg` data from the instance needs a dependent transport
  across that equality, where the index sits inside the type of each coefficient.
  That transport is not built.  Taking the data as a hypothesis keeps this file
  green and makes the missing step visible instead of burying it.

`hu` then comes from `ThomStepCSection.thomClass_ne_zero`, which needs no
topology at all: it is the degreewise identification read backwards.

## Main declarations

* `lixThomClass` — the Thom class of the mapping-torus bundle pair.
* `lixThomClass_ne_zero` — **it is nonzero**, which is the `hu` of Step C.
-/

open CategoryTheory
open GroupApproximation.STW59

namespace GroupApproximation.CharClass

noncomputable section

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

/-- **The Thom class of the mapping-torus bundle pair**, as the class whose top
Leray–Hirsch coefficient is `x`.  Built from the degreewise identification, which
is the `ThomDeg` data; no topology enters here. -/
def lixThomClass (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (n r : ℕ) {M : Fin (r + 1) → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod 2) (M i)]
    (g : ∀ i : Fin r, M (Fin.last r) →ₗ[ZMod 2] M i.castSucc)
    (jm : ↥(relCohomology (ZMod 2) (lixTotalPair hGc hGu) (lixPuncturedInTotal hGc hGu) n)
      →ₗ[ZMod 2] (∀ i, M i))
    (hinj : Function.Injective jm)
    (hrange : LinearMap.range jm = LinearMap.ker (ThomDeg.restrictMap g))
    (x : M (Fin.last r)) :
    ↥(relCohomology (ZMod 2) (lixTotalPair hGc hGu) (lixPuncturedInTotal hGc hGu) n) :=
  (ThomDeg.thomEquiv g jm hinj hrange).symm x

/-- **The Thom class is nonzero.**  This is the `hu` that
`topChernClass_ne_zero_odd_iso` takes, at `cc-lix-odd`'s objects.  It uses only
the degreewise identification, so it is free once that exists. -/
theorem lixThomClass_ne_zero (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) (n r : ℕ) {M : Fin (r + 1) → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod 2) (M i)]
    (g : ∀ i : Fin r, M (Fin.last r) →ₗ[ZMod 2] M i.castSucc)
    (jm : ↥(relCohomology (ZMod 2) (lixTotalPair hGc hGu) (lixPuncturedInTotal hGc hGu) n)
      →ₗ[ZMod 2] (∀ i, M i))
    (hinj : Function.Injective jm)
    (hrange : LinearMap.range jm = LinearMap.ker (ThomDeg.restrictMap g))
    {x : M (Fin.last r)} (hx : x ≠ 0) :
    lixThomClass hGc hGu n r g jm hinj hrange x ≠ 0 :=
  thomClass_ne_zero g jm hinj hrange hx

/-! Printed on every build. -/

#print axioms lixThomClass_ne_zero

end

end GroupApproximation.CharClass
