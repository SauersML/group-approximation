---
rg: 2
id: stw01-separable-ideal-does-not-force-sequential-qcau
kind: claim
title: A separable ideal need not have a sequential quasicentral approximate unit in its ambient algebra
distinct_from:
  stw01-sigma-unital-cuts-have-quasitracial-idempotence: that result obtains norm quasicentrality when the ambient algebra is separable; this counterexample shows that separability of the ideal alone is insufficient
artifacts:
  - research/artifacts/stw01-sigma-unital-extension-audit-2026-08-30.md
---

Let `H` be a separable infinite-dimensional Hilbert space and set

```text
A=B(H) direct_sum C,             I=K(H) direct_sum 0.
```

Then `I` is separable, but no sequential approximate unit for `I` is
norm-quasicentral in `A`.  This remains an obstruction in the presence of a
fixed nonzero bounded trace: for

```text
tau(T,lambda)=lambda
```

every positive contraction in `I` has zero `tau`-idempotence defect, yet no
increasing quasicentral approximate-unit sequence exists.

Thus the literal assertion that every separable ideal in an arbitrary
ambient algebra admits the requested sequential norm-quasicentral cuts is
false.  This does not obstruct
`stw01-sigma-unital-extensions-preserve-qt-linearity`, whose commutators
vanish only in the square seminorm of the ideal trace.
