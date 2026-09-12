---
rg: 2
id: atlas-q1920-psl5-double-natural-module-has-no-collision-seam
kind: claim
title: The doubled natural PSL5(2) module has no marked Q1920 collision seam
distinct_from:
  atlas-q1920-marked-simple-factor-is-at-least-ten-million: that excludes PSL5(2) itself among simple hosts below ten million; this excludes the two-copy natural linear realization in GL10(2), which lies beyond the simple-host census.
  atlas-cfsg-family-split-does-not-finitize-a8-carriers: that exhibits repeated-block ambient families abstractly; this is an exact collision-equation calculation for the marked Q1920 central quotient at multiplicity two.
---

Let `W` be the natural five-dimensional `F2[PSL5(2)]` module and restrict it
along either marked embedding

```text
Q/Z(Q) = 2^4:A5  -->  PSL5(2).
```

On `W^2`, for both Q markings, both ambient embedding classes, and all four
normalizer-orbit twists, there is no nonidentity `A=<r,u>`-central involution
`c` satisfying

```text
(c t)^3=1,       t c s c t^-1 c s t c=1.                (Q1920-2W-1)
```

Thus none of these sixteen doubled-natural slices can carry the collision
`S4`, and consequently none extends to the full marked packet.

This is a finite-multiplicity theorem only.  It does not rule out higher
multiplicity modules `W^m`: their centralizer algebras grow as
`M_(2m)(F2) x M_m(F2)`, so an all-multiplicity result requires controlling
matrix solutions of a fixed noncommutative polynomial system.

## Attempts

At multiplicity one `W|A` has indecomposable dimensions `2,2,1`, and the
unit group of `End_A(W)` has order six.  At multiplicity two the algebra has
dimension twenty and unit group order `120960`; the proof route exhausts
that full unit group rather than sampling it.  The same run also finds no
candidate `z` for the last forward cube, but the collision obstruction
already occurs before `z` is adjoined.
