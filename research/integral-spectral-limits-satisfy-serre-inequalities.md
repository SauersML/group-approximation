---
rg: 2
id: integral-spectral-limits-satisfy-serre-inequalities
kind: claim
title: Weak limits of symmetric integer matrix eigenvalue distributions obey every Serre inequality
distinct_from:
  determinant-conjecture-iff-serre-class-spectra: that says what the conjecture demands of group-ring spectra; this says which limiting measures automatically meet that demand
  fk-transfer-needs-uniform-log-integrability: that shows log determinants need not converge along moment limits; this is the one-sided inequality that does survive, when every approximant is integral
artifacts:
  - research/artifacts/determinant-conjecture-serre-class-2026-09-11.md
---

**ESTABLISHED (written proof, artifact Section 2).** Let `mu_k` be normalized
eigenvalue counting measures of symmetric integer matrices, all supported in
`[-C,C]`, converging weakly to `mu`. Then for every nonzero `Q in Z[x]`,

```text
integral_{Q != 0} log |Q| d mu >= 0.
```

The ingredients are integrality (nonzero eigenvalue products of `Q(B_k)` are
nonzero integers), the portmanteau bound `limsup mu_k(Z(Q)) <= mu(Z(Q))`,
and monotone convergence of `log max(|Q|, delta)` as `delta` decreases to 0.
No uniform integrability of the logarithm is needed. This is the mechanism
inside the Elek--Szabó proof, stated without any group.
