---
rg: 2
id: remote-scalar-face-cloud-fixed-point-proof
kind: route
title: Balance the three even-parity faces and choose incoherent nearest ties
target: face-exactify-cloud-majority-has-a-remote-scalar-fixed-point
requires: []
---

Use bits, with equality sign rounding at a tie choosing bit `0`.  Duplicate
the shared word `w=100` into every indexed face.  It violates `h_12` and
`h_13` and satisfies `h_23`.  Define the local nearest-face projection by

```text
 h_12 copies: (1,0) |-> (1,1),
 h_23 copies: (0,0) |-> (0,0),
 h_13 copy:   (1,0) |-> (1,1).                          (RFC1)
```

Each changed two-bit word is at Hamming distance one from its input and is
an exact even-parity word, hence is a nearest metric projection.  After
`Pi_A`, the occurrence multisets in the three equality clouds are

```text
 coordinate 1: {1,1,1},
 coordinate 2: {1,1,0,0},
 coordinate 3: {0,0,1}.                                (RFC2)
```

Their majority values, using the stated spectral-sign convention on the
tie in coordinate `2`, are `1,0,0`.  Therefore `Pi_B Pi_A(w)=w`.

The common kernel of `h_12,h_23,h_13` is `{000,111}`.  Hence `w` is one
coordinate, or relative distance `1/3`, from the exact shared variety.  It
violates three of the five indexed faces (the two `h_12` copies and the
single `h_13` face), so this remote fixed point has constant syndrome
energy rather than furnishing a low-energy microstate.
