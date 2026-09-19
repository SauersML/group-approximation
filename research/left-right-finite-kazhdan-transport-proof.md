---
rg: 2
id: left-right-finite-kazhdan-transport-proof
kind: route
title: Put the Kazhdan projection in the finite norm ultraproduct of left-right algebras
target: left-right-finite-kazhdan-transport
requires: []
artifacts:
  - research/artifacts/left-right-finite-coordinate-obstruction-2026-08-19.md
---

## Direct proof

Write `K_n=L^2(A_n,tau_n)` and `D_n=D_(tau_n)(A_n)`.  For every group
element,

```text
Ad U_n(g) = L_(U_n(g)) R_(U_n(g)^*) in U(D_n).
```

Operator-norm asymptotic multiplicativity of `U_n` implies operator-norm
asymptotic multiplicativity of these adjoint operators.  Pass to a free
ultrafilter and the norm ultraproduct `D_omega=prod_omega D_n`.  It is finite:
if `v^*v=1`, lift `v` to `v_n`, polar-correct to coordinate isometries, and
use finiteness of each `D_n` to make those isometries unitary.

The adjoint classes give an honest representation of `H` in `U(D_omega)` on
the Hilbert ultraproduct of the `K_n`.  A Kazhdan average for `Gamma` has an
isolated spectral value `1`; its spectral projection `P` belongs to
`D_omega` and has range the `iota(Gamma)`-fixed vectors.  If `V` is the class
of `Ad U_n(s)`, the one-sided subgroup inclusion gives

```text
P <= V P V^*.
```

The two projections are unitarily equivalent inside the finite algebra
`D_omega`, hence equal.  Therefore `V` preserves the fixed space.  Applying
this to the ultraproduct vector represented by `x_n` gives the transported
2-norm commutator convergence.  As in the matrix proof, choosing an
ultrafilter on any bad subsequence upgrades the ultrafilter conclusion to an
ordinary limit.

The only place the coordinate hypothesis enters is the sentence
`P <= VPV^*`, `P ~ VPV^*` implies equality.  The false arbitrary-trace route
put these projections in `M or JMJ` and incorrectly declared that algebra
finite; the present hypothesis says exactly that the correct coordinate
algebra is finite before taking the norm ultraproduct.
