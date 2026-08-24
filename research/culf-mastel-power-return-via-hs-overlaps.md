---
rg: 2
id: culf-mastel-power-return-via-hs-overlaps
kind: route
title: Use the scalar power-overlap compiler instead of a coherent dilation tail
target: culf-mastel-positive-density-power-return
requires:
  - finite-game-gap-makes-the-cyclic-acceptance-compressor-strict
  - block-encoded-acceptance-still-needs-corner-return
  - pauli-zero-atom-removes-acceptance-source-deficit
  - acceptance-return-is-one-corner-word
  - canonical-positive-density-hs-power-overlap-return
artifacts:
  - research/artifacts/adversarial-error-delocalization-program-2026-08-21.md
---

Use the Pauli zero atom to authenticate one head of fixed canonical density
and block-encode the cyclic acceptance contraction.  Matrix soundness gives
`rho<1`.  Choose fixed `L,N` with

```text
(N+1)alpha > 1+2 rho^(2L)/(1-rho^(2L)).
```

The overlap compiler returns the same authenticated `q` at the sampled
powers and supplies `(CPR1-HS)`.  Perfect completeness supplies the exact
nonzero carrier.  These are precisely the weaker sufficient clauses in
`culf-mastel-positive-density-power-return`; no coherent operator dilation
identity is needed.
