---
rg: 2
id: stw01-stable-ideal-extension-proof
kind: route
title: Kill a bounded quasitrace on the stable ideal and factor through its trace kernel
target: stw01-stable-ideal-extensions-force-qt-linearity
requires:
  - stw01-qt-invisible-ideal-extension-principle
artifacts:
  - research/artifacts/stw01-quasitrace-status-and-local-permanence-audit-2026-08-30.md
---

Let `tau` be a bounded 2-quasitrace on `A`; its restriction to `I` is a
bounded 2-quasitrace.  Stability supplies isometries `s_i in M(I)` with
pairwise orthogonal range projections.  For `a in I_+`, put

```text
a_i=s_i a s_i*,       i=1,...,n.
```

These elements are mutually orthogonal and commute.  Moreover they have
equal quasitrace: for `x=s_i a^(1/2) in I`, the defining identity gives

```text
tau(a)=tau(x*x)=tau(xx*)=tau(a_i).                      (SI2)
```

Commuting additivity and boundedness, with bound `C` on the positive unit
ball, now give

```text
n tau(a)=tau(sum_(i=1)^n a_i)
            <= C ||sum_(i=1)^n a_i||=C||a||.            (SI3)
```

Let `n` tend to infinity.  Thus `tau(a)=0` for every `a in I_+`.
The same argument applies to every bounded 2-quasitrace on `I`, so `I` is
bounded-quasitrace-invisible.  The quasitrace-invisible ideal extension
principle, together with the hypothesis on `Q`, now proves the claim.
