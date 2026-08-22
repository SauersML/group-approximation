---
rg: 2
id: finite-subgroup-hecke-literal-trace-proof
kind: route
title: Read the compressed projection trace from the finite packet coefficient
target: finite-subgroup-hecke-literals-cannot-block-escape
requires:
  - mipstar-bcs-tracial-nonru-exists
---

Since `q^2=q`, traciality gives `tau(qgq)=tau(gq)`.  The latter is the
identity coefficient of `gq`, namely `(FHL2)`.  Faithfulness proves `(FHL1)`.
For `q_H`, positivity of all coefficients proves the double-coset operator is
nonzero, and `g in H` makes it equal to `q_H`.  For minimal `q`, the corner
identity `qC[H]q=Cq` gives the zero/unit classification.

The Fourier-block construction `(FHL3)` is an exact projection calculation:
rank-one compression of `rho_1(g)=1` is one, while rank-one compression of
the reflection `sigma(t)` to the balanced vector `xi` is zero.  Both selected
irreducibles contain the nontrivial `C_2` character, so the trivial Fourier
block and hence augmentation vanish.  This proves sharpness.

Finally, applying `(FHL1)` to every variable literal puts the whole finite
BCS tuple in `qC[H]q`; its normalized canonical corner trace is a matrix
trace and hence Connes embeddable.  This contradicts the chosen BCS and
proves the compiler no-go.

