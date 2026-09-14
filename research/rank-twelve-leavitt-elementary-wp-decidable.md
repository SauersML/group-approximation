---
rg: 2
id: rank-twelve-leavitt-elementary-wp-decidable
kind: claim
title: The rank-twelve binary-Leavitt elementary group has decidable word problem and is infinite
distinct_from:
  binary-leavitt-unit-word-problem-decidable: that decides words in the unit group of the binary Leavitt algebra, a subgroup of the ring's invertible elements; this decides words in the rank-twelve elementary matrix group over the same ring, and adds infiniteness.
  rank-twelve-leavitt-simple-non-mf: that records simplicity, property (T) and the full MF radical of the same group; this records its algorithmic and cardinality properties, which that claim does not mention.
artifacts:
  - research/artifacts/boone-higman-mf-radical-bridge-2026-09-11.md
---

Let `R=L_(F_2)(1,2)` and `H=EL_12(R)`, the group of
`rank-twelve-leavitt-simple-non-mf`. Then

```text
H is infinite, and its word problem is decidable.            (RTW1)
```

Consequently `H` is recursively presented: the set of words over a finite
generating set that represent the identity is decidable, hence recursively
enumerable, and it is a defining set of relators.

Together with `rank-twelve-leavitt-simple-non-mf` this makes `H` an
**infinite finitely generated computably presented simple group**, that is,
an admissible input to `boone-higman-conjecture` and to its equivalent
restriction `infinite-simple-input-boone-higman`. What distinguishes it from
the inputs usually considered is recorded in `fp-simple-full-mf-radical-group`:
`H` has full MF radical, so any Boone--Higman envelope of `H` inherits that
property.

DERIVATION
rank-twelve-leavitt-elementary-wp-proof
