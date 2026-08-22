---
rg: 2
id: leavitt-transport-drift-and-l7-atomic-no-go
kind: claim
title: Two-generator relation transport needs degree at least three and has no atomic length-seven compiler
artifacts:
  - research/leavitt-transport-drift-and-l7-atomic-no-go-proof.md
  - research/artifacts/check-leavitt-degree-three-atomic-transport.py
distinct_from:
  leavitt-omega-has-an-explicit-distorted-target: that supplies the exact source law and distorted target; this proves a lower bound on the number of translated relations and exhausts the minimal atomic encoder.
  leavitt-second-nielsen-direct-bridge-collision-no-go: that fences direct equality of two bridges in the degree-two length-six system; this treats two simultaneous generator identifications and the minimal degree-three system.
---

In an index-`d` paired rewrite, all `d` translated relators have stable-letter
exponent one, so their zero-drift difference lattice has rank at most `d-1`.
Two-generator transport therefore requires `d>=3` (and `d>=4` at even
length).

For length seven and degree three, all three cyclic sign types and all
332,280 full-support assignments in the atomic packet alphabet
`{a,e,q,x_13(s_0),p^(+-1),(qp)^(+-1),1}` have been checked exactly.  After
every possible one-`z` pivot elimination, none yields two direct
identifications of the same coefficient-copy pair.  Composite packets, or
the degree-four length-eight system, are therefore genuinely necessary for
this transport architecture.
