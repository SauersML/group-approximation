---
rg: 2
id: hs-defect-gap-ratio-padding-invariant-proof
kind: route
title: Compute normalized Frobenius mass in the active summand
target: hs-defect-gap-ratio-padding-invariant
requires: []
artifacts:
  - research/artifacts/weak-mf-hs-profile-audit-2026-08-30.md
---

## Direct proof

Write

```text
E(a,b)=phi(a)phi(b)-phi(ab).
```

Since the identity block is exactly multiplicative,

```text
phi'(a)phi'(b)-phi'(ab)=E(a,b) directSum 0_m.
```

With `Tr` denoting the unnormalized trace,

```text
||E(a,b) directSum 0_m||_(2,d+m)^2
 = Tr(E(a,b)^*E(a,b))/(d+m)
 = (d/(d+m)) ||E(a,b)||_(2,d)^2,
```

which is `(PI1)`.  Also

```text
tr_(d+m)(phi(g) directSum 1_m)
 = (d tr_d(phi(g))+m)/(d+m),
```

so taking `1-Re` proves `(PI2)`.  Division gives `(PI3)`, and the common
factor `rho` also factors through a maximum over finitely many numerator
terms.  End proof.
