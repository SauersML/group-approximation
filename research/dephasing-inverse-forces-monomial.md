---
rg: 2
id: dephasing-inverse-forces-monomial
kind: claim
title: Entrywise dephasing can respect inverses only near the monomial locus
artifacts:
  - research/artifacts/hyperlinear-extreme-breakthroughs-2026-08-18.md
---

For `U in U(d)` put `P_U(i,j)=|u_ij|^2`.

**Theorem.** If

```text
||P_U P_U^T-I||_{2,d} <= eps,
```

then there is a monomial unitary `M` such that

```text
d_2(U,M)^2 <= 2 eps.
```

Thus any one-basis phase-erasure scheme that manages to preserve the inverse
law has already forced the input unitary close to the monomial category. The
usual unistochastic map is not a hidden shortcut around the common-basis
problem; preserving the group inverse is itself an integrality condition.
