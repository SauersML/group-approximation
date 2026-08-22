---
rg: 2
id: projective-transfer-proves-canonical-iwahori-transfer
kind: route
title: Apply projective arithmetic transfer and orient its signs on the Iwahori edge
target: canonical-iwahori-projection-commutant-transfer
requires:
  - projective-commutant-transfer-for-arithmetic-pair
  - iwahori-edge-orientation-removes-projective-sign-branch
---

For a canonical Iwahori projection sequence put `V_n=2P_n-1`.  Ordinary
commutation with the first vertex implies zero asymptotic projective energy
against its fixed generators.  Apply projective commutant transfer to the
asymptotic presentation of `A=SL_2(Z[1/2])`, once for each fixed generator
word of the second modular vertex.  This gives `(IER3)`.

The common Iwahori edge lies in the first vertex, so `(IER1)` also holds.
The sign-resolution claim converts projective centrality on the exact second
vertex to ordinary centrality.  Replacing `V_n` by `P_n=(1+V_n)/2` changes
commutator norms by the factor `1/2`, proving `(CIP3)`.

