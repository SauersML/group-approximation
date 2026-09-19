---
rg: 2
id: projective-transfer-proves-canonical-iwahori-transfer
kind: route
title: Apply projective arithmetic transfer and orient its signs on the approximate Iwahori edge
target: canonical-iwahori-projection-commutant-transfer
requires:
  - projective-commutant-transfer-for-arithmetic-pair
  - quantitative-iwahori-projective-sign-resolution
---

For a canonical Iwahori projection sequence put `V_n=2P_n-1`.  Ordinary
commutation with the first vertex implies zero asymptotic projective energy
against its fixed generators.  Apply projective commutant transfer to the
asymptotic presentation of `A=SL_2(Z[1/2])`, once for each fixed generator
word of the second modular vertex.  This gives projective trace-square energy
tending to zero on a fixed presentation of that vertex.

The common Iwahori edge lies in the first vertex, so its ordinary commutators
with `P_n` tend to zero.  The second vertex is only an approximate
representation, not an exact one; apply
`quantitative-iwahori-projective-sign-resolution` with its relator defect,
projective generator energy, and edge commutator energy.  Its two strict
thresholds hold eventually and it gives ordinary second-vertex commutation.
Replacing `V_n` by `P_n=(1+V_n)/2` changes commutator norms by the factor
`1/2`, proving the canonical projection transfer conclusion.

The exact theorem `iwahori-edge-orientation-removes-projective-sign-branch`
is the zero-defect boundary of this argument.  The quantitative version is
load-bearing for microstates because no exactification of the modular vertex
is available at this stage.
