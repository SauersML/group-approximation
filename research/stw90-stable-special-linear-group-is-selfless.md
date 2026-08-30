---
rg: 2
id: stw90-stable-special-linear-group-is-selfless
kind: claim
title: The stable integral special linear group is selfless and strictly comparing
distinct_from:
  stw99-problem-xc-cstar-simple-strict-comparison: this is one explicit positive group, not the universal assertion.
  vigdorovich-linear-selflessness: every finite odd-rank stage is covered by Vigdorovich, but the stable union here is proved nonlinear and therefore is not covered as a linear group.
  stw91-countable-free-direct-sum-is-selfless: both use directed unions and are nonlinear non-acylindrical examples, but this group is the nested stable matrix group rather than a restricted direct product; its reduced algebra is not presented as an infinite tensor product.
artifacts:
  - research/artifacts/stw90-strict-comparison-group-frontier-2026-08-30.md
---

Let

```text
SL_infinity(Z) = union_{m>=1} SL_{2m+1}(Z),
```

where the connecting map is `A |-> diag(A,I_2)`.  Its reduced group
C*-algebra is selfless and hence simple, stably rank one, uniquely
2-quasitracial, and strictly comparing by its canonical trace.

The countable group `SL_infinity(Z)` is nonlinear over every field and is not
acylindrically hyperbolic.  It is therefore an explicit positive XC instance
outside the linear and acylindrically hyperbolic group classes; unlike the
restricted direct sum of free groups, this example does not arise from the
countable tensor-product construction.
