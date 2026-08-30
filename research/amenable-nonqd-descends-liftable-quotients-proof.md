---
rg: 2
id: amenable-nonqd-descends-liftable-quotients-proof
kind: route
title: Descend amenability and use the contrapositive of QD pullback
target: amenable-nonqd-descends-liftable-quotients
requires:
  - amenable-trace-descends-through-locally-liftable-quotient
artifacts:
  - research/artifacts/stw10-amenable-trace-frontier-2026-08-30.md
---

The prerequisite theorem makes `tau_B` amenable.  If `tau_B` were QD, and
`psi_n:B -> M_{k(n)}` were norm-multiplicative trace approximations, then

```text
psi_n o q:A -> M_{k(n)}
```

would be norm-multiplicative trace approximations for `tau_A`, because `q` is
a *-homomorphism.  This would make `tau_A` QD, contrary to the hypothesis.
Hence `tau_B` is not QD.

Local liftability is used only for amenability descent.  No norm-multiplicative
map is pushed through the quotient.
