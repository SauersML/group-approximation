---
rg: 2
id: bs14-common-reflection-exit-bound-proof
kind: route
title: Charge both exit equations to the already paid common-source rank
target: bs14-polar-exits-retain-the-common-physical-reflection
requires:
  - common-physical-reflection-pays-two-exit-gram-seam
  - two-source-gram-alignment-pays-frequency-not-mode-purity
  - bs14-energy-threshold-active-passive-ledger
---

After source alignment, `F_i` and `H_i` are contractions from the same
`r`-dimensional source.  Since the rounded physical `X` is unitary,

```text
||XF_i-H_i||_F^2
 <=(||XF_i||_F+||H_i||_F)^2<=4r.
```

Sum over the two rows and use the active rank estimate
`r/d<=c^(-2)e^(1/2)` to obtain `(PER4)`.  No invariant hull and no packet
decomposition enters.  With `X=X*`,
`common-physical-reflection-pays-two-exit-gram-seam` bounds the mixed Gram
block by the sum of these two exit errors, proving the final assertion.
