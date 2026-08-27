---
rg: 2
id: atlas-a4-classical-mixture-trace-separator-proof
kind: route
title: Regular traces turn the finite collision audit into one separating hyperplane
target: atlas-a4-classical-mixture-trace-separator
requires:
  - atlas-a4-classical-collision-gap-one-fifth
---

Fix one inner or outer alignment `phi`.  In the regular representation of
`A8`, every nonidentity group element has normalized trace zero.  Hence for any
word `u` in the two chart factors,

```text
||u-1||_(2,tau_phi)^2
 = 0  if u(phi)=1,
 = 2  if u(phi)!=1.                                    (1)
```

There are two cases.

If `q(phi)=1`, `atlas-a4-classical-collision-gap-one-fifth` says that at least
six of the thirty pair-cubes are nontrivial.  By `(1)` their contribution to
the first sum is at least `6*2=12`.

If `q(phi)!=1`, the collision term alone contributes

```text
6 ||q-1||_2^2 = 6*2 = 12.
```

Thus `(A4-MIX-SEP)` holds for every individual alignment.  For a convex mixture
`tau_nu=sum_phi nu(phi) tau_phi`, squared unitary defect is affine in the trace:

```text
||u-1||_(2,tau_nu)^2 = 2-2 Re tau_nu(u)
                      = sum_phi nu(phi) ||u-1||_(2,tau_phi)^2.
```

Averaging the pointwise inequality proves `(A4-MIX-SEP)` for every `nu`.
Expanding all thirty-six weighted defect units gives the equivalent hyperplane
form

```text
sum_j Re tau_nu(w_j) + 6 Re tau_nu(q) <= 30.
```

No operator-level direct-sum decomposition is used: this is purely a statement
about the convex hull of the thirty-one regular alignment trace profiles.
