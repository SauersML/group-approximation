---
rg: 2
id: stw99-lv-dual-trace-scaling-spectrum-cocycle-invariant
kind: claim
title: The dual trace-scaling spectrum of a flow is invariant under cocycle conjugacy
artifacts:
  - research/artifacts/stw99-late-band-audit-2026-08-31.md
---

Let `alpha:R -> Aut(A)` be a flow such that the cone of densely defined lower
semicontinuous traces on `A rtimes_alpha R` has a unique nonzero ray.  If `tau`
spans that ray, write

```text
tau after hat(alpha)_s = c_alpha(s) tau.
```

Then `c_alpha:R -> (0,infinity)` is independent of the choice of `tau`, and it
is invariant under cocycle conjugacy of flows.  In particular, when
`c_alpha(s)=exp(-beta_alpha s)`, the exponent `beta_alpha` is a
cocycle-conjugacy invariant with the original parametrization of `R` fixed.

This statement concerns the dual action on the crossed product.  It does not
assert that a distinguished KMS state itself is unchanged by a cocycle
perturbation; that assertion is false even for inner flows on matrix algebras.

