/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.BHPalomar.GraphProducts.Insert
import GroupApproximation.BHPalomar.GraphProducts.ProductInput

/-!
# BFFHZ Question 3.1: graph products of PBH groups are PBH

`question31_of_envelopeInput : EnvelopeInput → Question31`.

The one remaining hypothesis is `EnvelopeInput`, which is BFFHZ (arXiv:2503.21882v2)
Theorem C (i) ⇒ (iv) combined with Theorem E: a group with an action of type (A) embeds in a
group `H` such that `Aut_H(H ∗ F₂)` satisfies PBH. Everything else is proved here from Mathlib:

* the embedding of `X *_C (C × K)` in `Aut_H(H ∗ F₂)` (Steps 1–5, `Embedding`);
* the decomposition of a graph product into iterated retract amalgams (Step 6, `Insert`);
* closure of PBH under direct products (`ProductInput`).
-/

namespace GroupApproximation.BHPalomar.GraphProducts

/-- **BFFHZ Question 3.1, positive answer, from the two named inputs.** -/
theorem question31_of_inputs (hE : EnvelopeInput) (hP : ProductInput) : Question31 :=
  question31_of_retractAmalgamClosure (retractAmalgamClosure_of_inputs hE hP)

/-- **BFFHZ Question 3.1, positive answer**, conditional only on BFFHZ Theorems C and E. -/
theorem question31_of_envelopeInput (hE : EnvelopeInput) : Question31 :=
  question31_of_inputs hE productInput_holds

end GroupApproximation.BHPalomar.GraphProducts
