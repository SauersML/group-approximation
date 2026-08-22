---
rg: 2
id: complete-overlay-glues-exact-ldpc-face-pvms
kind: claim
title: The complete overlay glues every exact repeated-LDPC face PVM into one global code PVM
distinct_from:
  quadratic-repetition-supports-complete-commutation-overlay: that proves exact coordinate commutation with bounded occurrence; this identifies and reconstructs the resulting global codeword measurement.
  positive-rate-tanner-tests-have-contextual-models: that uses only local face overlaps; this adds all logical pair commutations and proves that no exact contextual model remains.
  operator-unique-neighbor-cosystolic-rounding: that is the approximate dimension-independent correction problem; this settles its zero-defect agreement statement only.
---

In the exact repeated-LDPC presentation, impose copy equalities, every local
binary codeword PVM, and the complete logical pair overlay of
`quadratic-repetition-supports-complete-commutation-overlay`.  Then all copies
of logical coordinate `i` equal one reflection `Q_i`, and all `Q_i,Q_j`
commute.

For every full binary string `c in {0,1}^L`, define

```text
P_c=prod_(i=1)^L (I+(-1)^(c_i)Q_i)/2.                     (COG1)
```

The `(P_c)` form a joint PVM.  Every parity relation forces `P_c=0` unless
`c` is a codeword: on `P_c`, the corresponding parity product has eigenvalue
`(-1)` for a violated check but equals `I` by the presentation.  Finally,
`binary-face-pvm-is-determined-by-coordinate-reflections` shows that every
original local face PVM is the marginal of `(P_c)`.

Therefore no exact contextual family of local PVMs survives the equality,
parity, and complete-pair overlays, regardless of Tanner expansion.  The
remaining same-PVM gate is entirely quantitative: average approximate
relations must be corrected to the exact coordinate situation above with a
modulus independent of `L`.
