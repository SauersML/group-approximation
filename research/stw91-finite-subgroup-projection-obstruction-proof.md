---
rg: 2
id: stw91-finite-subgroup-projection-obstruction-proof
kind: route
title: Compare averaging projections by their canonical traces
target: stw91-finite-subgroup-projection-obstruction
requires:
  - robert-tracial-selfless-regularity
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

Robert's theorem says that tracial selflessness forces strict comparison,
so (1) follows.  Cuntz subequivalence of projections agrees with
Murray--von Neumann subequivalence: there is a projection `q <= e_K`
equivalent to `e_H`.  Therefore

```text
[e_K]-[e_H]=[e_K-q] in K_0(C*_r(G))_+,
```

which is (2).  Taking contrapositives gives the stated counterexample test.

**Trust boundary.**  The only imported input is Robert's implication from
tracial selflessness to strict comparison.  The averaging-projection,
trace, and ordered-`K_0` calculations are direct.
