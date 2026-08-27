---
rg: 2
id: km-su-reservoir-scalarization-no-go-proof
kind: route
title: Insert a balanced near-identity special unitary in the regular multiplicity commutant
target: km-su-reservoir-defeats-discrete-scalarization
requires:
  - three-chart-loop-retains-free-multiplicity-holonomy
---

Every regular finite-parahoric chart is `lambda_P tensor I_m`; its full
multiplicity unitary group `I tensor U(m)` commutes with all label matrix
units and all restricted subgroup actions. Therefore multiplying one chord
by `I tensor W_(m,t)` changes only the fundamental-cycle holonomy. The two
eigenvalue blocks in `(KSR1)` have equal size, so their determinants cancel
and `det(W_(m,t))=1`. The normalized trace is `cos(t)`, giving `(KSR2)` by
the standard identity

```text
||W-I||_2^2=2-2 Re tau(W).
```

For `0<t<pi`, neither eigenvalue is one, proving `(KSR3)`. All label-side
intertwiners and cocycles are unchanged because the inserted factor is the
identity on `L`; in particular it contributes no finite projective-label or
Schur-multiplier class.

For the distinct-phase variant choose real numbers

```text
-t<=theta_1<...<theta_m<=t,       sum_j theta_j=0,
```

and put `W=diag(e^(i theta_j))`. Then `W in SU(m)`, `||W-I||_2<=t`, and
every eigenspace is one-dimensional. A reducing projection on which `W` is
scalar lies in one eigenspace and therefore has rank at most one. This proves
the large-corner assertion and the stated scope.
---
