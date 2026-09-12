import GroupApproximation.CharClass.LemmaTwoStepDLix
import GroupApproximation.CharClass.LIXChernSplit
import GroupApproximation.CharClass.ParityEvenLixSplitting

/-!
# Step D's data with the splitting pinned

Lane `cc-lix-odd`.

`WuStepDLix` takes the Chern splitting `S` as a free field.  `cc-wu` and `cc-projective`
found that this is a seam rather than a convenience: `hslice` is stated *against whichever
`S` the assembler chose*, and `hslice_of_props` proves that statement only when `S` is
`Wu.chernSplitOfGraded`.  Any other splitting of the same class leaves `hslice` reopened,
even though the two classes agree.

So the field has a forced value, and a structure that lets a consumer pick differently is a
trap.  `WuStepDPinned` removes the choice: `S` is `cc-projective`'s `lixChernSplit`, which
is `chernSplitOfGraded` at the mapping torus by definition, so the field and its discharge
agree by construction.

`WuStepDLix` stays exported; per the fleet rule a published signature does not move, and
anything already built against it is unaffected.

## Main results

* `WuStepDPinned` — Step D's data with `S` forced.
* `WuStepDPinned.toWuStepDLix` — hence the published form.
* `stepD_of_wuPinned` — **Step D** over it.
* `WuStepDSlice` — the same with the **splitting principle** discharged too, by
  `cc-wu`'s `hasSplitting_lix`, leaving only the generators and the slice identification.
* `stepD_of_wuSlice` — **Step D** over that.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-- **Step D's data, with the splitting pinned.**  Compared with `WuStepDLix`, the field
`S` is gone: it is `lixChernSplit`, the only value for which `hslice` is dischargeable. -/
structure WuStepDPinned (dd : Fin ℓ → ℕ)
    (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ) (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) where
  /-- The splitting principle, with the flag space hidden. -/
  hsplit : Wu.HasSplitting (lixN dd)
    (lixChernOf (lixChern dd) (mappingTorus Vmat G circHoriz circHeight))
  /-- The generators of the projective factors. -/
  gen : Fin ℓ → TotalH (KnTwo.YTop (baseY dd))
  /-- The slice identification, against the pinned splitting. -/
  hslice : ∀ q : ℕ,
    Wu.splitA dd (lixChernSplit dd G hGc hGu) q
      = (sliceClass (Finset.univ : Finset (Fin ℓ)) gen dd).coeff q

/-- The pinned data gives the published form. -/
def WuStepDPinned.toWuStepDLix
    {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ} {hGc : Continuous G}
    {hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)} (D : WuStepDPinned dd G hGc hGu) :
    WuStepDLix dd (lixChernOf (lixChern dd)
      (mappingTorus Vmat G circHoriz circHeight)) where
  S := lixChernSplit dd G hGc hGu
  hsplit := D.hsplit
  gen := D.gen
  hslice := D.hslice

/-- **Step D**, over the pinned data. -/
theorem stepD_of_wuPinned (hd : ∀ j, Even (dd j))
    (data : ∀ (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ) (hGc : Continuous G)
      (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)), WuStepDPinned dd G hGc hGu) :
    ∀ G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ, Continuous G →
      (∀ m, IsCornerUnitary (Vmat m) (G m)) →
      lixTopClass (lixChern dd) (mappingTorus Vmat G circHoriz circHeight) = 0 :=
  stepD_of_wuLix (lixChern dd) (fun X => cartanOf_holds X) hd
    fun G hGc hGu => (data G hGc hGu).toWuStepDLix

/-! ## The splitting principle, discharged

`cc-wu`'s `hasSplitting_lix` is `WuStepDPinned.hsplit`'s type character for character, over
exactly the three arguments the structure already takes, so the field is not an input at
all.  Behind it the splitting principle is now unconditional: over a compact non-empty base
a bundle of constant positive rank has a splitting, and the flag tower's own compactness
and non-emptiness are derived rather than assumed.

What is left is the generators, which are a choice rather than an obligation, and the slice
identification. -/

/-- **Step D's data with both forced fields gone.** -/
structure WuStepDSlice (dd : Fin ℓ → ℕ)
    (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ) (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) where
  /-- The generators of the projective factors. -/
  gen : Fin ℓ → TotalH (KnTwo.YTop (baseY dd))
  /-- The slice identification, against the pinned splitting. -/
  hslice : ∀ q : ℕ,
    Wu.splitA dd (lixChernSplit dd G hGc hGu) q
      = (sliceClass (Finset.univ : Finset (Fin ℓ)) gen dd).coeff q

/-- The slice data gives the pinned data, the splitting principle coming from `cc-wu`. -/
def WuStepDSlice.toWuStepDPinned
    {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ} {hGc : Continuous G}
    {hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)} (D : WuStepDSlice dd G hGc hGu) :
    WuStepDPinned dd G hGc hGu where
  hsplit := Wu.hasSplitting_lix G hGc hGu
  gen := D.gen
  hslice := D.hslice

/-- **Step D**, over the generators and the slice identification alone. -/
theorem stepD_of_wuSlice (hd : ∀ j, Even (dd j))
    (data : ∀ (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ) (hGc : Continuous G)
      (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)), WuStepDSlice dd G hGc hGu) :
    ∀ G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ, Continuous G →
      (∀ m, IsCornerUnitary (Vmat m) (G m)) →
      lixTopClass (lixChern dd) (mappingTorus Vmat G circHoriz circHeight) = 0 :=
  stepD_of_wuPinned hd fun G hGc hGu => (data G hGc hGu).toWuStepDPinned

end GroupApproximation.CharClass
