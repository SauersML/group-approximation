---
rg: 2
id: binary-schur-branch-payment-via-19243-holonomy
kind: route
title: Put collision 19243 in the relative inner frame of the two retained child branches
target: binary-schur-toeplitz-one-branch-hs-payment
requires:
  - binary-schur-head-embeddings-are-relative-inner-holonomies
  - atlas-a4-packet-four-rectangle-normal-form
  - atlas-word-19243-is-kernel-relation
  - atlas-a4-root-energy-ellipse-ceiling
---

Tensor each forbidden sector with the fixed regular-A8 chart and choose the
two coordinate automorphisms in `(BRH3)` so their relative projective frame is
the atlas return frame.  Use the thirty shortest A4 pair-cubes for the branch
return and impose collision `q_19243` in the quotient.  Tree gauge fixing
leaves exactly the four rectangle holonomies of
`atlas-a4-packet-four-rectangle-normal-form`.

The binary Schur embedding supplies two equal-scale child copies.  The
collision relation makes a zero-energy return incompatible with a nontrivial
relative frame, while `atlas-a4-root-energy-ellipse-ceiling` gives the needed
dimension-independent quantitative payment.  Assign the paid atlas branch as
the exit copy and retain the other as the next active carrier.  The resulting
one-exit inequality is `(BHP2)`.

This route explains why the 19243 computation and the Toeplitz programme are
not competing constructions.  Skolem--Noether shows that relative holonomy is
the only nonstationary datum a unital binary coefficient embedding can carry,
and the A4 packet is the current finite compiler for charging precisely that
datum.

## Phase-orientation gap

`projective-atlas-cannot-orient-transverse-branch-phase` shows that the route
as stated cannot orient the two children. Its relative datum is `[W] in PGL`,
so `W` and `iW` have identical Atlas packet and collision data. But that phase
rotation exchanges the complementary D8 deficits `D_T,D_S`. Thus 19243 may
charge total nontrivial projective holonomy, but it cannot decide which child
is the paid exit in `(BHP2)`. This route remains open only with an additional
odd, phase-sensitive lift of the return frame tied to the payload; adjoining
the full branch-flip Pauli cell is not such a lift because it consumes the
Schur surplus.
