import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.FanBridge
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.WordMultiplier.Multiplier
import GroupApproximation.Meta.AxiomGuard

/-!
# Frame cone at rank four, unconditional

Khanh (arXiv:2609.08428), Prop. `prop:frame-cone`:

> Let `E` be a finite set of frames of lengths `k_i ≤ r-2` in `L^r`. Then there is `v ∈ L^r`
> such that `(v, f_i)` is a frame for every `i ∈ E`.

Route: lane 08 (`LeavittK2.exists_word_multiplier`, Khanh Lemma `lem:word-multiplier`) is exactly
`FrameCone.WordMultiplierStatement`; plugging it into `frame_cone_four_of_wordMultiplier` and
`binaryLeavittFrameConeFour_of_wordMultiplier` gives `frame_cone_four` (`r = 4`, `k ≤ 2`) and the
fan interface `FrameFan.BinaryLeavittFrameConeFourStatement` of lane `sk-leavitt-10`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone

open GroupApproximation

/-- Lane 08 closes the word-multiplier interface. -/
theorem wordMultiplierStatement : WordMultiplierStatement :=
  fun _ a ha => exists_word_multiplier a ha

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.wordMultiplierStatement

/-- **Frame cone at rank four (Khanh Prop. 4.2, `k ≤ 2`).** -/
theorem frame_cone_four
    (F : Finset (List (Fin 4 → BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))))
    (hF : ∀ f ∈ F, f.length ≤ 2 ∧ IsFrame f) :
    ∃ v, ∀ f ∈ F, IsFrame (v :: f) :=
  frame_cone_four_of_wordMultiplier wordMultiplierStatement F hF

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.frame_cone_four

/-- **Lane `sk-leavitt-10` interface**: the rank-four frame cone in the vertex/edge form. -/
theorem binaryLeavittFrameConeFour : FrameFan.BinaryLeavittFrameConeFourStatement :=
  binaryLeavittFrameConeFour_of_wordMultiplier wordMultiplierStatement

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.binaryLeavittFrameConeFour

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone
