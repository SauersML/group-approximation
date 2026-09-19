---
rg: 2
id: leavitt-area-eight-parity-breaking-dichotomy
kind: claim
title: Any surviving eight-cell Leavitt picture must expose an odd coefficient identity, usually of length five or seven
artifacts:
  - research/artifacts/leavitt-area-eight-parity-residue-2026-08-21.md
distinct_from:
  leavitt-even-region-short-atlas-has-area-ten: that excludes the entire even-region short-atlas sector; this classifies the only topology left when parity fails.
  leavitt-short-atlas-does-not-close-six-cells: that treats six relator vertices and a length-four mixed boundary; this starts at eight vertices after all 36 even length-eight residuals are eliminated.
---

All 36 shortest even-region residual words from the eight-cell curvature
census are nontrivial in `G_0*G_1`.  Hence an actual eight-cell kernel
picture must have at least one ODD internal coefficient region.

There are no coefficient identities of length one or three in the six
corner labels.  Consequently every odd internal identity has length at
least five.  Since an eight-vertex cubic spherical picture has six faces
of total length `24`, exactly one of the following holds:

1. at least two internal faces are odd, in which case one of them has
   length `5` or `7`;
2. exactly one internal face is odd, the outer face is odd, and the internal
   identity has length in `{5,7,9,11,13,15}`.

Thus the first exact symbolic target beyond the 36 length-eight words is an
odd length-five or length-seven identity.  A one-odd-face escape may defer
the first identity as far as length fifteen, but only by spending the second
odd face on the outer boundary.

This is a complete curvature classification of the parity-breaking residue,
not a universal area-ten theorem.  Perfectness of the coefficient factors
prevents extending the short-atlas parity to a global character, so the odd
sector cannot be discarded formally.

