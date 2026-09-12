---
rg: 2
id: stw99-lxxvi-compact-cancellation-counterexample-proof
kind: route
title: Let Z-stabilization cancel two distinct compact Cuntz classes
target: stw99-lxxvi-compact-cancellation-counterexample-criterion
requires: []
---

The first assertion is immediate: the displayed pair is a failure of
injectivity of `Cu(iota_A)`.

For the criterion, functoriality sends equality of `[p]` and `[q]` in
`K_0(A)` to

```text
[p tensor 1_Z]=[q tensor 1_Z] in K_0(A tensor_min Z).
```

Equality in the Grothendieck group means that for some projection `r` over
`A tensor_min Z`,

```text
(p tensor 1_Z) directSum r
  Murray--von Neumann equivalent to
(q tensor 1_Z) directSum r.
```

Cancellation of projections removes `r`, so `p tensor 1_Z` and
`q tensor 1_Z` are Murray--von Neumann equivalent.  Projection classes agree
in the Cuntz semigroup exactly under stable Murray--von Neumann equivalence,
whereas `[p]!=[q]` by hypothesis.  Thus `Cu(iota_A)` is not injective.
