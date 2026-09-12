---
rg: 2
id: fct8-left-lift-and-rotated-defect-proof
kind: route
title: Compare rank-one and left-multiplier lifts, then rotate one sparse defect through every leaf
target: fct8-left-lift-and-rotated-defect-firewall
requires:
  - free-compressor-tree-has-constant-first-hit-mover-mass
  - left-rank-amplification-is-not-a-fixed-sector
  - tracial-superoperator-self-copy-has-no-macroscopic-excess
---

The rank-one lift has pointwise-fixed range and trace `1/d^2`; summing it
over the `2^n` leaves gives `(FLR1)`.  Directly compute the rank, covariance,
and normalized Hilbert--Schmidt norm of `L_X` for `(FLR2)--(FLR6)`.  The
superoperator trace formula

```text
tr_K(Ad_W)=|tau_d(W)|^2
```

and `1-|z|^2<=2(1-Re z)` prove `(FLR7)`.

For `(FLR8)`, choose equal coordinate blocks and permutation matrices sending
the support of `R` onto each block.  Conjugation sends `L_R` exactly to the
corresponding `L_(P_i)`, so compression by `F_i` loses nothing.  Normalized
trace then gives `m/(2m)=1/2`, while the original defect has squared norm
`1/(2m)`.
