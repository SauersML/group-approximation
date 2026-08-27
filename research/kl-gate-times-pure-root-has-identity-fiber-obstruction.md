---
rg: 2
id: kl-gate-times-pure-root-has-identity-fiber-obstruction
kind: claim
title: A KL gate times one cyclic pure-chart KL root always leaves the identity fiber odd
distinct_from:
  two-kl-gate-orbit-has-identity-fiber-obstruction: that treats products of two coordinate copies of the mixed gate; this treats the two other KL coefficient types in both orders.
  kl-gate-corner-test-is-an-even-unit-fiber-audit: that treats single gates and single roots; this treats their minimal distinct-type products.
  inverse-packet-conjugator-must-mix-s-and-t-charts: that only excludes wholly pure-chart conjugators; every word here contains the mixed gate and needs the sharper identity-fiber obstruction.
artifacts:
  - research/artifacts/kl-gate-in-c3-corner-chart-2026-08-21.md
  - research/artifacts/verify-kl-gate-c3-corner.py
---

Let `q_i` be a cyclic coordinate conjugate of the mixed KL gate and let
`a_j`, respectively `f_j`, be a cyclic conjugate of `x_12(s_0)`, respectively
`x_12(t_1)`.  For every index pair and every word

```text
x in {q_i a_j, q_i f_j, a_j q_i, f_j q_i},
```

exact Bergman normal form gives

```text
[1]Delta=1,
([1](A P_(x^-1)), [1](P_x B), [1](P_x P_(x^-1)))=(0,0,0).
```

Hence the inverse-pair defect has identity coefficient one in all 1,600
cases, and none of these minimal distinct-type mixed conjugators solves the
corner equation.
