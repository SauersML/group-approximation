---
rg: 2
id: toeplitz-defect-tensor-dilution-audit-proof
kind: route
title: Apply trace cyclicity and exhibit the rectangular Morita escape
target: toeplitz-defect-needs-square-decoding
requires:
  - positive-toeplitz-head-is-square-defect-or-rectangular-escape
  - mixed-steinberg-loops-admit-morita-rectangular-model
  - canonical-packet-traces-do-not-place-old-commutant-density
---

Apply the inequality `(PTH2)` to the contractions in `(TDT2)` to obtain
`(TDT3)`.  If `tau(P)>=q>0`, at least one named coefficient defect is at
least `q/2`, and their squared sum is at least `q^2/2`, independently of
matrix dimension and tensor placement.

For the converse semantic boundary, take `F=E direct-sum H`, let `X:E->F`
be inclusion and `Y:F->E` projection, and let `P` project `F` onto `H`.
Then `YX=1_E` and `XY=1_F-P` exactly.  The source and target units are
different objects, so trace cyclicity cannot compare them.  Rectangular
block transvections realize every composable Steinberg multiplication
triangle exactly.  This proves `(TDT4)` and isolates same-reservoir
authentication as the missing group-microstate statement.
