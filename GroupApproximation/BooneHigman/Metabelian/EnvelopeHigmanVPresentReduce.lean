import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVSwapGenReduce
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVPresentSection
import GroupApproximation.Meta.AxiomGuard

/-!
# The swap-section statements from bare finite presentability of `V_d` (lane bh-met-71c)

This file reduces `SwapGenShortSectionStatement`, `SwapGenSectionStatement` and
`HigmanVSwapSectionStatement` (the `hswap` input of the Boone–Higman root in
`ChainWiredFrontierThree.lean`) to the existing Statement `HigmanVFinFPStatement`
(`EnvelopeHigmanVAlphabet.lean`): for every `d ≥ 2`, `higmanThompsonV (Fin d)` is finitely
presented.  The step is general (`higmanVPresent_section_of_fp`): a finitely presented group has
the relator/section data on *every* finite generating family, by the Tietze/B. H. Neumann step
`Tietze.isFinitelyNormallyGenerated_ker` and a `surjInv` section.

**LOUD: the remaining gap `HigmanVFinFPStatement` is logically EQUIVALENT to
`SwapGenShortSectionStatement`, not weaker.**  The converse is proved here as
`higmanVPresent_finFP_of_swapGenShortSection` (via the existing `higmanVFinSection_of_swapGenShort`
and `higmanVFinFP_of_section`).  The gap is strictly smaller in proof content only: it is exactly
Higman's 1974 theorem as bare finite presentability, with no choice of generators, no relator
bookkeeping and no section.  It is also implied by `HigmanVFPStatement`
(`higmanVPresent_finFP_of_higmanVFP`), which is itself equivalent to it via `higmanVFP_of_fin`.
Per the brief, the existing interface is reused instead of a new `HigmanVPresent…Statement`.

*Truth.*  `HigmanVFinFPStatement` is true (Higman, *Finitely presented infinite simple groups*,
1974).  It is not proved here.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Every finite generating family, from Higman's theorem.**  If each `V_d` (`d ≥ 2`) is
finitely presented, then every finite generating family of `V_d` has finitely many relators
carrying a unital intertwining section. -/
theorem higmanVPresent_swapGen_of_finFP (h : HigmanVFinFPStatement) :
    SwapGenSectionStatement := by
  intro d hd n g hg
  haveI : Group.IsFinitelyPresented ↥(higmanThompsonV (Fin d)) := h d hd
  exact higmanVPresent_section_of_fp g hg

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVPresent_swapGen_of_finFP

/-- **The lane target from Higman's theorem.**  The short cone swaps carry the section data,
given that each `V_d` is finitely presented. -/
theorem swapGenShortSection_of_higmanVFinFP (h : HigmanVFinFPStatement) :
    SwapGenShortSectionStatement :=
  swapGenShort_of_swapGen (higmanVPresent_swapGen_of_finFP h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.swapGenShortSection_of_higmanVFinFP

/-- **The root's `hswap` from Higman's theorem.**  The swap-section statement consumed by
`finitelyPresentedMetabelianStatement_of_frontierThree` follows from finite presentability of
each `V_d`. -/
theorem higmanVPresent_swapSection_of_finFP (h : HigmanVFinFPStatement) :
    HigmanVSwapSectionStatement :=
  higmanVSwapSection_of_swapGen (higmanVPresent_swapGen_of_finFP h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVPresent_swapSection_of_finFP

/-- **LOUD converse.**  The short-swap section statement gives finite presentability of each
`V_d`, so `HigmanVFinFPStatement` and `SwapGenShortSectionStatement` are equivalent. -/
theorem higmanVPresent_finFP_of_swapGenShortSection (h : SwapGenShortSectionStatement) :
    HigmanVFinFPStatement :=
  higmanVFinFP_of_section (higmanVFinSection_of_swapGenShort h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVPresent_finFP_of_swapGenShortSection

/-- Higman's theorem over all finite nontrivial alphabets gives it over the alphabets `Fin d`. -/
theorem higmanVPresent_finFP_of_higmanVFP (h : HigmanVFPStatement) : HigmanVFinFPStatement := by
  intro d hd
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
  exact h (Fin d)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVPresent_finFP_of_higmanVFP

/-- The lane target from Higman's theorem over all finite nontrivial alphabets. -/
theorem swapGenShortSection_of_higmanVFP (h : HigmanVFPStatement) :
    SwapGenShortSectionStatement :=
  swapGenShortSection_of_higmanVFinFP (higmanVPresent_finFP_of_higmanVFP h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.swapGenShortSection_of_higmanVFP

end GroupApproximation.BooneHigman.Metabelian.Envelope
