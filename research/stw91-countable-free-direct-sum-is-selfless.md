---
rg: 2
id: stw91-countable-free-direct-sum-is-selfless
kind: claim
title: The countable restricted direct sum of F2 is selfless, C*-simple, nonlinear, and not acylindrically hyperbolic
distinct_from:
  stw99-problem-xci-cstar-simple-selfless: this is one explicit positive example and does not settle the universal C*-simple-group question.
  vigdorovich-linear-selflessness: the group here is proved nonlinear, so Vigdorovich's linear-group theorem does not apply to it.
  agkp-acylindrically-hyperbolic-rd-groups-selfless: the group here is proved not acylindrically hyperbolic, so it is outside AGKP's geometric hypothesis.
artifacts:
  - research/artifacts/stw91-selfless-group-frontier-2026-08-30.md
---

Let

```text
G = direct_sum_{m in N} F_2,
```

the group of finite-support sequences in countably many copies of the
two-generator free group.  Then `(C*_r(G),tau_G)` is selfless.  Consequently
`G` is C*-simple.  Moreover, `G` is not isomorphic to a subgroup of
`GL_d(k)` for any finite `d` and any field `k`, and `G` is not
acylindrically hyperbolic.

Thus the directed-union mechanism produces a concrete countable positive
case outside both the linear and acylindrically hyperbolic classes.  This is
a new proof route, not a claim of a previously unknown example: Ozawa's
countable exact tensor-product theorem also applies to the infinite tensor
product description of `C*_r(G)`.
