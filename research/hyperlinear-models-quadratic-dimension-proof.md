---
rg: 2
id: hyperlinear-models-quadratic-dimension-proof
kind: route
title: Read the operator-norm inequality through the two norm comparisons
target: hyperlinear-models-need-quadratic-dimension
requires:
  - full-mf-radical-linear-relator-inequality
  - defect-saturation-full-mf-radical
artifacts:
  - research/artifacts/hs-defect-gap-and-padding-2026-09-07.md
---

## Proof

In normalized Hilbert--Schmidt norm on `M_d`, `||a||_2 <= ||a||_op` and
`||a||_op <= sqrt d ||a||_2`.

Let `D_2(U) >= 1`.  Then `D_infty(U) >= D_2(U) >= 1`.  Apply `(LIN)` and the
second comparison to each relator:

```text
1 <= D_infty(U) <= C d_infty(U) <= C sqrt d  d_2(U),
```

where the middle step uses that the relator list of `(LIN)` is contained in
`R`.  Squaring gives `d >= 1/(C^2 d_2(U)^2)`.

For a microstate sequence of a hyperlinear `Q`, `d_2 -> 0`, so the floor
tends to infinity.
