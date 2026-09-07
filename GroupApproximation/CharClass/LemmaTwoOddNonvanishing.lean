import GroupApproximation.CharClass.LemmaTwoGlue
import GroupApproximation.CharClass.LemmaTwoStepDLix
import GroupApproximation.CharClass.SliceValueV

/-!
# Lemma 2 from the raw odd-side nonvanishing, with Step D discharged

Lane `cs-endpoint` of the STW Problem LIX program.

`CharClass/ParityEvenLemmaTwoClosed.lean`'s `lemmaTwoHolds_of_chain` reduces
`LIX.LemmaTwoHolds` to a `chain` argument in the `ThomChainThom` record shape ---
`cc-thom`'s excision-and-chart route to Step C's odd side.  `cc-lix-odd`'s own
`lix_topClass_ne_zero_of_local` (behind `LIXStepCOddThom.lean`'s
`lix_topClass_ne_zero_of_thom`) is a **different** proof of the same conclusion,
`LemmaTwoTopClass.lean`'s `stepC_of_chain` consumes exactly its per-stage,
per-mapping-torus nonvanishing --- `stepC_of_thomChainThom` is literally
`stepC_of_chain chern fun G hGc hGu hGe => ne_zero_of_thomChainThom ...` --- so the
record is an avoidable detour: routing through it costs the excision and chart
data (`rel`, `chart`, `exc`, `chartIso`) that `lix_topClass_ne_zero_of_local`'s route
never needed.

This file takes Step C already in `lixTopClass`-wrapped form --- `stepC_of_chain`'s
conclusion, which is what `cs-endpoint`'s `LIXStepCOddWired.lean` produces once its
three open hypotheses are supplied and `gamma` is instantiated at the mapping
torus's Chern class --- and supplies Step D unconditionally, exactly as
`ParityEvenLemmaTwoClosed.lean` and `ParityEvenVSlice.lean` already do: `cc-wu`'s
`Wu.cartanTotal`, `LIX.even_lixDD`, and `cc-steenrod`'s `vSliceValue_sliceGen` at
`LH.sliceGen`, `LIX.lixDD_pos`.  None of those three is per-stage or hypothetical,
so `LemmaTwoInput` assembles with no argument beyond the odd-side nonvanishing.

## Main result

* `lemmaTwoHolds_of_oddNonvanishing` --- **`LIX.LemmaTwoHolds`, over the raw odd-side
  nonvanishing alone.**
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

/-- **Step D, unconditionally, at every stage.**  `cc-wu`'s Cartan formula and the
tower's evenness are theorems, and `cc-steenrod`'s value statement for `V` closes
the last open field of `data_of_vSliceValue`, so nothing here is a hypothesis. -/
theorem lixStepD_unconditional (j : ℕ)
    (G : baseM (LIX.lixDD j) → Matrix (VIdx (LIX.lixDD j)) (VIdx (LIX.lixDD j)) ℂ)
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    lixTopClass (lixChern (LIX.lixDD j)) (mappingTorus Vmat G circHoriz circHeight) = 0 :=
  stepD_of_wuLix (lixChern (LIX.lixDD j)) Wu.cartanTotal (LIX.even_lixDD j)
    (data_of_vSliceValue
      (fun j' => ⟨LH.sliceGen (LIX.lixDD j') (LIX.lixDD_pos j'),
        vSliceValue_sliceGen (LIX.lixDD j') (LIX.lixDD_pos j')⟩) j)
    G hGc hGu

/-- **`LIX.LemmaTwoHolds`, from the raw odd-side nonvanishing alone.**  The single
hypothesis is Step C at every stage, in the shape `cs-endpoint`'s
`LIXStepCOddWired.lean`'s `lix_topClass_ne_zero_of_three` produces once its three
open fields land; Step D is the theorem `lixStepD_unconditional` above. -/
theorem lemmaTwoHolds_of_oddNonvanishing
    (h : ∀ j : ℕ,
      ∀ G : baseM (LIX.lixDD j) → Matrix (VIdx (LIX.lixDD j)) (VIdx (LIX.lixDD j)) ℂ,
        Continuous G → (∀ m, IsCornerUnitary (Vmat m) (G m)) →
        (∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) →
        lixTopClass (lixChern (LIX.lixDD j)) (mappingTorus Vmat G circHoriz circHeight)
          ≠ 0) :
    LIX.LemmaTwoHolds :=
  lemmaTwoHolds_of fun j =>
    ⟨TotalH (lixN (LIX.lixDD j)), inferInstance, lixTopClass (lixChern (LIX.lixDD j)),
      h j, fun G hGc hGu => lixStepD_unconditional j G hGc hGu⟩

end GroupApproximation.CharClass
