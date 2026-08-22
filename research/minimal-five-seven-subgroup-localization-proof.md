---
rg: 2
id: minimal-five-seven-subgroup-localization-proof
kind: route
title: Project to the support subgroup and exclude every smaller odd partner rank
target: minimal-five-seven-partner-cannot-escape-support-subgroup
requires:
  - dykema-heister-juschenko-bounded-rank-direct-finiteness
artifacts:
  - research/artifacts/minimal-five-seven-subgroup-localization-2026-08-21.md
---

Decompose `F_2[G]` over right `K`-cosets.  Left multiplication by
`alpha in F_2[K]` preserves every summand.  Since the identity lies in the
base summand, the `F_2[K]`-component `beta_K` of `beta` satisfies

```text
alpha beta_K=1.
```

Augmentation gives `eps(beta_K)=1`, so its support size is odd and at most
seven.  It cannot be one: then `beta_K` is a group basis unit and the equality
would force `alpha` to be its inverse, contradicting support five.  It cannot
be three because the universal `(3,5)` direct-finiteness result would give
`beta_K alpha=1`; comparing with `alpha beta_K=1` would make `alpha` a unit,
and then the original right inverse is unique, so `beta=beta_K` and the
reverse product is one.  The same argument excludes support five using the
`(5,5)` result.

Therefore `beta_K` has support seven.  Since `beta` itself has exactly seven
support terms, no term lies outside `K`, proving the claim.

