import GroupApproximation.CharClass.CartanMidFourChainMap

/-!
# The four slot terms of the fourfold differential

The differential of a nested tensor is the sum of the four per-slot boundaries,
with no signs, and the middle-four interchange does not touch the slots.  So both
sides of the interchange's chain-map property are the same four terms, grouped
differently.

This module named those four terms.  It no longer defines them, and the reason
is worth recording, because it was the whole difficulty of the interchange.

The first definitions computed each slot's output degree from the input degrees.
That made the two sides of the identity spell the same number two ways: after
splitting `a₁` and `a₃`, one side carried `a₁' + 1 + a₃` and the other
`(a₁' + a₃) + 1`.  Those are propositionally but not definitionally equal for a
variable summand, because addition on the naturals recurses on its second
argument; no normalisation lemma bridges them, since the successor is written as
an addition rather than as `Nat.succ`; and the definitional escape is shut,
because any such check unfolds the tensor's structure literal and exceeds the
budget.  Twenty-six probes failed on that and none of them failed on the
mathematics.

The definitions now live in `CartanPadTen`, carrying every degree of the result
as a parameter and absorbing the constraints into `padTen`, which returns `0` off
the diagonal.  Then neither side spells a sum at all, and both reach the same
term.  This module is the entry point for the chain that follows:
`CartanPadTen`, `CartanMidFourGroup`, `CartanMidFourTgt`, `CartanMidFourSrc`,
and `CartanMidFourChainMap`, whose endpoints are `tensorD_midSwap` and
`midSwapHom`.
-/
