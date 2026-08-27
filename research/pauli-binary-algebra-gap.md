---
rg: 2
id: pauli-binary-algebra-gap
kind: claim
title: Fixed Pauli carrier has a dimension-free binary-algebra distance gap
distinct_from:
  leavitt-multiplicative-trace-floor: This is a two-projection coefficient-algebra obstruction; the other uses four contractions and three products.
  outer-pvm-synchronization: This is the completed finite-matrix endpoint after membership is obtained; the other asks to synchronize transition measurements from group microstates.
artifacts:
  - GroupApproximation/Leavitt/PauliCarrierBinaryGap.lean
  - notes/TRUE_PAULI_CARRIER_BINARY_ALGEBRA_GAP.md
---

If projections `E,F` satisfy `tau(E)=1/8` and `tau(F)=1/4`, then the squared
normalized `L^2` distance from `F` to the binary algebra
`W*(E)=span{E,1-E}` is at least `3/28`.  In the canonical Pauli packet the
exact overlap improves the squared floor to `3/16`.

Thus it is enough for a microstate decoder to force binary-algebra
membership of the transported carrier; orientation and a full Leavitt
family need not be recovered.
