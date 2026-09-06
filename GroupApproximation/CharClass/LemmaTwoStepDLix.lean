import GroupApproximation.CharClass.ParityEvenTransport
import GroupApproximation.CharClass.LemmaTwoStepCThom

/-!
# Step D at the geometric model, and both steps about one class

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3).

`CharClass/LemmaTwoStepD.lean` states Step D over an abstract base `N` with three
projections, because the even side was developed at `KnTwo.NTop Y = (Y × S⁵) × S¹` while
this lane works at `lixN dd = S¹ × (S⁵ × Y)`.  Both sides were green about **different
spaces**, which no probe on either side could have detected.  `cc-wu`'s
`ParityEvenTransport.lean` closes that seam by carrying the even side across
`Wu.lixIso`, so Step D can now be stated at `lixN` directly.

## What this file adds

`WuStepDLix` is Step D's data at `lixN`.  Against `WuStepDData` it drops the four space
parameters, the two sphere generators and the three projections, and `a` and `b` are no
longer fields at all: they come out of the `ChernSplit` as `Wu.splitA` and `Wu.splitB`.

`WuStepDData` and `stepD_of_wu` are **unchanged and still exported**, per the fleet rule
that a published signature does not move; a consumer already built against the abstract
form is not broken by this.

## Both steps, one class

`lemmaTwoInput_lix` is the payoff: Step C from `ThomChainThom` and Step D from
`WuStepDLix`, about the *same* `lixTopClass`, on the *same* space.  Feeding it to
`lemmaTwoHolds_of` gives `LIX.LemmaTwoHolds`.

What remains open in it is exactly three things, all `cc-projective`'s: the Thom class
datum `hu` and the nonvanishing `hne` on the odd side, and the `ChernSplit` on the even
side.  Everything else is a theorem.

## Main results

* `WuStepDLix` — Step D's data at `lixN`.
* `stepD_of_wuLix` — **Step D** at the real objects.
* `lemmaTwoInput_lix` — **both steps about one class**, at one space.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. Step D's data, at `lixN` -/

/-- **What `cc-wu` needs, at this lane's space.**  Compared with `WuStepDData`: no `N`,
`Y`, `S₁`, `S₅`, no projections, no sphere generators, and no `a`/`b` fields.  The one
genuinely open field is `S`, `cc-projective`'s splitting of the Chern classes. -/
structure WuStepDLix (dd : Fin ℓ → ℕ) (γ : ℕ → TotalH (lixN dd)) where
  /-- **Open** (`cc-projective`): each mod-2 Chern class splits, with its two coefficients
  in the degrees the grading forces. -/
  S : KnTwo.ChernSplit (baseY dd) (fun k => TotalH.map (Wu.lixIso dd).inv (γ k))
  /-- The splitting principle, with the flag space hidden. -/
  hsplit : Wu.HasSplitting (lixN dd) γ
  /-- The generators of the projective factors. -/
  gen : Fin ℓ → TotalH (KnTwo.YTop (baseY dd))
  /-- The slice identification. -/
  hslice : ∀ q : ℕ,
    Wu.splitA dd S q = (sliceClass (Finset.univ : Finset (Fin ℓ)) gen dd).coeff q

/-- **Step D's conclusion**, in the rank index this lane works in.  `lixRank dd` unfolds to
`(∑ⱼ dⱼ) + 3`, which is `cc-wu`'s index, so no conversion is needed. -/
theorem WuStepDLix.gamma_top_eq_zero (hC : Wu.CartanTotal) (hd : ∀ j, Even (dd j))
    {γ : ℕ → TotalH (lixN dd)} (D : WuStepDLix dd γ) :
    γ (lixRank dd) = 0 :=
  Wu.lix_gamma_top_eq_zero dd hC γ D.S D.hsplit D.gen hd D.hslice

/-! ## 2. Step D at the real objects -/

/-- **Step D**, over the mapping tori, at `lixN`. -/
theorem stepD_of_wuLix (chern : LixChernDeg dd) (hC : Wu.CartanTotal)
    (hd : ∀ j, Even (dd j))
    (data : ∀ (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ), Continuous G →
      (∀ m, IsCornerUnitary (Vmat m) (G m)) →
      WuStepDLix dd (lixChernOf chern (mappingTorus Vmat G circHoriz circHeight))) :
    ∀ G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ, Continuous G →
      (∀ m, IsCornerUnitary (Vmat m) (G m)) →
      lixTopClass chern (mappingTorus Vmat G circHoriz circHeight) = 0 :=
  fun G hGc hGu => (data G hGc hGu).gamma_top_eq_zero hC hd

/-! ## 3. Both steps, one class, one space -/

/-- **`LemmaTwoInput` with both steps at the geometric model.**

Step C is `cc-thom`'s chain in the Thom-class shape; Step D is `cc-wu`'s data carried to
`lixN`.  Both speak about `lixTopClass chern` on `lixN dd`, so the contradiction is between
two statements about literally the same class.

The open inputs are three, all `cc-projective`'s: `hu` and `hne` inside `ThomChainThom`,
and `S` inside `WuStepDLix`. -/
theorem lemmaTwoInput_lix (chern : LixChernDeg dd) (hdd : ∀ j, 0 < dd j)
    (hC : Wu.CartanTotal) (hd : ∀ j, Even (dd j))
    (chain : ∀ (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ) (hGc : Continuous G)
      (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)),
      (∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) →
      ThomChainThom dd
        (chern (mappingTorus Vmat G circHoriz circHeight)
          (continuous_mappingTorus_lix hGc) (isStarProjection_mappingTorus_lix hGu)
          (lixRank dd)))
    (data : ∀ (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ), Continuous G →
      (∀ m, IsCornerUnitary (Vmat m) (G m)) →
      WuStepDLix dd (lixChernOf chern (mappingTorus Vmat G circHoriz circHeight))) :
    LemmaTwoInput dd :=
  ⟨TotalH (lixN dd), inferInstance, lixTopClass chern,
    stepC_of_thomChainThom chern hdd chain, stepD_of_wuLix chern hC hd data⟩

/-! ## 4. The axiom report -/

#print axioms stepD_of_wuLix

#print axioms lemmaTwoInput_lix

end GroupApproximation.CharClass
