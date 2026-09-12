---
rg: 2
id: leavitt-three-gate-candidate-is-injective
kind: claim
title: The paired three-gate length-six Leavitt candidate satisfies coefficient injectivity
artifacts:
  - research/artifacts/leavitt-three-gate-nielsen-amalgam-proof-2026-08-21.md
distinct_from:
  leavitt-length-six-three-gate-weight-survivor: that proves only that the standard relative weight test fails; this gives a different normal-form proof that the candidate is nevertheless injective.
  leavitt-paired-quotient-passes-relative-weight-test: that fences the earlier two-gate candidate by a weight function; this fences the three-gate candidate by a Nielsen amalgam.
---

For the paired quotient

```text
Gamma=(G_0*G_1*<z>)/<<
 a_0 z q_0p_1 z e_0 z^(-1),
 a_1 z q_1 z p_0e_1 z^(-1)>>,
```

the canonical map `G_0*G_1 -> Gamma` is injective.  Hence the length-six
three-gate word does not normally generate the degree-two kernel and cannot
be a Kervaire--Laudenbach counterexample.
