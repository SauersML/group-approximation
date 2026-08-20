---
rg: 2
id: two-chart-jacobi-action-holonomy
kind: claim
title: A finite two-chart holonomy absorbs the truncated Jacobi parameter drift
distinct_from:
  jacobi-congruence-clifford-tower: that requests the whole finitely presented tower; this isolates its remaining compatibility problem after the exact two-chart geometry is known.
---

Using the `P_n,Q_n` atlas from `truncated-weyl-two-chart-boundary`, construct
finitely many word templates which:

1. implement upper elementary transformations in the `Q` chart and lower
   elementary transformations in the `P` chart;
2. use the Fourier/coordinate-swap word to pass between the charts;
3. absorb the exact parameter drift `r |-> ur` by the tape compressor;
4. transport the local signs as `J_n=t^nJ_0t^(-n)`; and
5. make the resulting one-cell chart holonomy pay normalized-HS energy, with
   constants independent of `n` and polynomial word-derivation cost.

Together with the fixed relative-Kazhdan words, this supplies the compatible
finite syntax required by `jacobi-congruence-clifford-tower`.

## Attempts

- The exact atlas geometry, including its fixed one-qubit transverse pieces,
  is `truncated-weyl-two-chart-boundary`; sign transport is
  `conjugate-local-signs-preserve-marked-carrier`. What remains is to spell a
  finite compressor presentation for `(TWC3)` and prove that approximate
  chart changes cannot dump the mismatch into the two transverse cells at
  every level. The latter should use the existing polar overlap theorem and
  bounded-overlap energy accounting, but the cyclic product has not been
  estimated.

