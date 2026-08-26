---
rg: 2
id: atlas-pointwise-column-coercivity-no-go-proof
kind: route
title: Evaluate tracial residual-column coercivity in the exact Leavitt factor
target: atlas-pointwise-column-coercivity-misses-moving-injection
requires:
  - atlas-radius-nine-packet-gram-sos-is-tracial
  - atlas-six-relator-factor-retains-half-nontrivial-s3-mass
---

Suppose the pointwise estimate `(PCC2)` is derived by fixed C-star/Gram
positivity.  Squaring it gives the positive-operator inequality

```text
A^*A<=L^2 sum_r R_r^*R_r.                            (PCP1)
```

By `atlas-radius-nine-packet-gram-sos-is-tracial`, the same derivation is
valid in every finite tracial realization of the packet.  Evaluate it in the
exact Leavitt factor.  Every one of the six residuals `R_r` is zero, while
`atlas-six-relator-factor-retains-half-nontrivial-s3-mass` gives

```text
tau(A^*A)=||A||_2^2>=1/2.                            (PCP2)
```

Equation `(PCP1)` instead forces `A^*A=0`, a contradiction.  Hence fixed
tracially functorial residual-column coercivity cannot supply the moving
singular injection.

For clarity, if a genuinely matrix-only proof of `(PCC2)` exists, then for
`xi` in the source high space and all six residual low spaces,

```text
t||xi||<=||Axi||<=L||Rxi||<L sqrt(6) kappa t||xi||.
```

Taking `kappa<1/(L sqrt(6))` forces `xi=0`; codimension then proves `(SCI3)`
with constant one.  Thus the calculation invalidates exactly the fixed
tracial proof route, not the matrix-only pointwise target.


