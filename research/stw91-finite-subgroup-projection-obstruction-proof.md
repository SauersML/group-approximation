---
rg: 2
id: stw91-finite-subgroup-projection-obstruction-proof
kind: route
title: Compare averaging projections by their canonical traces
target: stw91-finite-subgroup-projection-obstruction
requires: []
artifacts:
  - research/artifacts/stw91-selfless-group-frontier-2026-08-30.md
---

For a finite subgroup `H`, elementary multiplication in the group ring gives
`e_H=e_H^*=e_H^2`, so `e_H` is a projection.  The canonical trace extracts
the identity coefficient, hence

```text
tau_G(e_H)=1/|H|.                                     (3)
```

For a projection `p`, its dimension value is `d_tau(p)=tau(p)`.  Thus
`|H|>|K|` and (3) give

```text
d_tau(e_H) < d_tau(e_K).
```

Strict comparison gives (1).  Cuntz subequivalence of projections agrees with
Murray--von Neumann subequivalence: there is a projection `q <= e_K`
equivalent to `e_H`.  Therefore

```text
[e_K]-[e_H]=[e_K-q] in K_0(C*_r(G))_+,
```

which is (2).  Taking contrapositives gives the stated counterexample test.

**Trust boundary.**  The averaging-projection, trace, and ordered-`K_0`
calculations are direct.  The route assumes strict comparison exactly as
stated in the claim; selflessness enters only through Robert's separately
recorded implication when this certificate is applied to Problem XCI.
