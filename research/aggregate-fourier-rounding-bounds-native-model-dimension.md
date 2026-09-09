---
rg: 2
id: aggregate-fourier-rounding-bounds-native-model-dimension
kind: route
title: Sum Fourier rounding errors before using finite projection ranks
target: finite-abelian-table-traces-force-linear-dimension
requires:
  - binary-leavitt-units-generated-by-c3-and-c2-cubed
artifacts:
  - research/artifacts/finite-abelian-fourier-dimension-pressure-2026-09-08.md
---

For each character of the finite abelian group form the Fourier
average `P_chi` of the approximate table. Parseval applied to
the inversion residuals and the averaged multiplication
residuals gives

```text
sum_chi ||P_chi^*-P_chi||_2^2<=epsilon^2,
sum_chi ||P_chi^2-P_chi||_2^2<=epsilon^2.
```

Symmetrization followed by spectral rounding gives projections
`Q_chi` with aggregate error at most `11 epsilon/2`. Their
traces have total mass at least `1-D` and Euclidean norm at
most `m^(-1/2)*(sqrt(1+(m-1)*a_0^2)+D)`.

For each actual matrix projection, `q_chi=tr Q_chi` satisfies
`q_chi^2>=q_chi/n`, by integer rank. Summing gives the stated
dimension bound without asserting that the `Q_chi` commute or
form a PVM.

For the native application, put independent two-dimensional
order-three companion blocks inside a degree-zero matrix block
with an additional fixed coordinate. Every nonidentity element
of the resulting `C_3^r` is conjugate in the full Leavitt unit
group to the native `c`: collapse its nonzero free companion
multiplicity and its positive fixed summand separately by
prefix-code module isomorphisms. Native generation supplies
words for these finitely many units and conjugators. Literal
table and conjugacy rows then give exactly the finite hypotheses
of the general matrix bound.
