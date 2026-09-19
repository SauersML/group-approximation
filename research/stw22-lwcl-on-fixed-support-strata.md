---
rg: 2
id: stw22-lwcl-on-fixed-support-strata
kind: claim
title: Local weighted corner lifting holds on every continuous fixed-support stratum
distinct_from:
  stw22-finite-dimensional-colouring-from-local-lifts: that theorem assumes local weighted corner lifting for arbitrary small-support positive fields; the present theorem proves the assumption only where the support projection is continuous and has locally constant trace.
  stw22-zero-dimensional-trivial-field-trace-continuity: that theorem tolerates arbitrary support jumps by clopen approximation; the present theorem works over positive-dimensional neighbourhoods but requires a fixed Murray--von Neumann support stratum.
artifacts:
  - research/artifacts/stw22-lwcl-fixed-support-stratum-audit-2026-08-30.md
---

Let `R` be the hyperfinite `II_1` factor, let `e in R` be a projection, and
let `Z` be a topological space.  Suppose

```text
a:Z -> R_+
```

is operator-norm bounded and `2`-norm continuous.  Put
`p(z)=supp(a(z))`.  Assume that, on a neighbourhood of `z_0`,

```text
z |-> p(z) is 2-norm continuous,
tau(p(z))=r<tau(e) is constant.                          (FSS)
```

Then there is a neighbourhood `O` of `z_0` and a `2`-norm-continuous map
`w:O->R` such that

```text
w(z)^*w(z)=a(z),       supp(w(z)w(z)^*)<=e.              (FSL)
```

Thus the local weighted corner-lifting hypothesis `(LWCL)` holds on every
continuous fixed-support stratum.  In particular, the finite-dimensional
and property-`C` coloured gluing theorems are unconditional for a spectral
cut whose support field satisfies `(FSS)` on the local-lift domains.

The result does not prove `(LWCL)` across varying support trace or a
discontinuous support field.  Those cross-stratum directions are the exact
remaining analytic hinge in the positive-dimensional method.

