---
rg: 2
id: property-t-free-el20-collapse-transfers-to-el12
kind: claim
title: Full MF collapse of binary-Leavitt EL20 transfers internally to EL12
artifacts:
  - GroupApproximation/Leavitt/LeavittRankEquivalence.lean
  - GroupApproximation/Sofic/FullRadicalClosureProperties.lean
distinct_from:
  property-t-free-st20-collapse-transfers-to-el12: that first pushes a Steinberg collapse through the canonical projection; this starts directly with EL20 and needs only the explicit binary-prefix rank equivalence.
---

Let `R=L_(F_2)(1,2)`.  The implication

```text
Rad_MF(EL_20(R))=EL_20(R)
  ==> Rad_MF(EL_12(R))=EL_12(R)                         (ERT1)
```

is Property-`(T)`-free and internal.  The complete left-comb binary prefix
codes give an explicit group equivalence

```text
EL_20(R) ~= EL_12(R).
```

Transport the full MF radical across this equivalence using the internal
surjective-image/equivalence calculus.  No Steinberg lift, `K_2` statement,
canonical trace, or literature theorem occurs.

