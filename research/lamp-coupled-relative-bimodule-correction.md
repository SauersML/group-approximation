---
rg: 2
id: lamp-coupled-relative-bimodule-correction
kind: claim
title: Correct the covariance free-product action while preserving its exact module restriction
refuted_by: [aperiodic-module-forbids-prescribed-hs-bimodule-extension]
artifacts:
  - research/artifacts/whole-module-kazhdan-mixed-word-audit-2026-08-21.md
distinct_from:
  relative-kazhdan-bimodule-requires-whole-module-covariance: that proves the uncorrected factor action does not descend; this asks for the precise lamp-coupled correction that evades the circularity.
  finite-presentation-must-expose-whole-module-with-uniform-defect: that decodes and rounds the abelian module itself; this starts after that rounding and corrects the actor--module Hilbert--Schmidt action.
---

**REFUTED for the intended aperiodic augmentation host.**

`aperiodic-module-forbids-prescribed-hs-bimodule-extension` proves that any
finite-dimensional representation of `M rtimes A` with the exact prescribed
module restriction

```text
X |-> rho(s m)Xrho(m)^*
```

forces `rho(s m)=rho(m)` for every `m`.  Requiring the extension for every
actor generator makes the finite spectral support of `rho` pointwise
`A`-fixed; augmentation-module aperiodicity then forces `rho` to be trivial.
Thus no such correction can preserve the nontrivial lamp seed.  The
Kazhdan-set displacement clause is irrelevant to this obstruction.

The former target was:

For the chosen finitely presented augmentation actor host, start with the
exact same-dimensional module representation `rho` produced by global
abelian rounding and an exact actor representation `pi`.  For every actor
generator `s`, correct the free-product Hilbert--Schmidt action from
`relative-kazhdan-bimodule-requires-whole-module-covariance` to a genuine
representation `Theta_s` of `Gamma=M rtimes A` such that:

1. its restriction to `M` remains exactly
   `X |-> rho(s m)Xrho(m)^*` for every `m`;
2. on one fixed relative Kazhdan set `Q`, the displacement of `pi(s)` is
   bounded by a dimension-independent modulus of the original finite
   presentation defect.

This is the precise surviving property-`(T)` gate.  Once supplied,
`relative-kazhdan-bimodule-upgrades-finite-covariance` gives uniform
whole-module covariance and hence the character transport energy.
