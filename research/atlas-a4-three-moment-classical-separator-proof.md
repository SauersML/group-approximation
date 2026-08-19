---
rg: 2
id: atlas-a4-three-moment-classical-separator-proof
kind: route
title: The two-context hitting property becomes a three-coordinate trace inequality
target: atlas-a4-three-moment-classical-separator
requires:
  - atlas-a4-two-context-collision-gap
---

Fix one inner or outer chart alignment `phi`.  If `q(phi)!=1`, then regular
trace gives

```text
||q-1||_(2,tau_phi)^2 = 2,
```

so `(A4-3M-SEP)` holds.  If `q(phi)=1`,
`atlas-a4-two-context-collision-gap` says at least one of `u(phi),v(phi)` is
nonidentity.  Its regular-trace squared defect is `2`, so the same inequality
again holds.

For a convex mixture `tau_nu=sum_phi nu(phi) tau_phi`, each squared unitary
defect is affine in the trace:

```text
||x-1||_(2,tau_nu)^2
 = 2-2 Re tau_nu(x)
 = sum_phi nu(phi) ||x-1||_(2,tau_phi)^2.
```

Averaging the pointwise inequality proves `(A4-3M-SEP)`.  Expanding its three
terms gives

```text
6 - 2 Re(tau_nu(u)+tau_nu(v)+tau_nu(q)) >= 2,
```

which is exactly `(A4-3M-HYP)`.
