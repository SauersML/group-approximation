---
rg: 2
id: finite-table-quantum-classical-hamming-gap
kind: claim
title: Some finite table is solvable to arbitrary unitary accuracy but not by permutations
refuted_by:
  - unseparated-finite-table-gap-is-impossible
distinct_from:
  regular-finite-table-quantum-classical-hamming-gap: that is the intended regular-character statement, with identity and pair-separation errors included explicitly; this literal statement optimizes multiplication error alone.
---

**REFUTED AS WRITTEN.** There is no finite partial multiplication table `T`
and `c > 0` such that

```text
inf { multiplicative defect of a unitary model of T }      = 0,
inf { Hamming multiplicative defect of a permutation model of T } >= c.
```

Indeed, assign every symbol of `T` to the identity unitary, respectively to
the identity permutation. Every tested product then holds exactly, so both
infima are zero for every `T`. The intended nontrivial question is
`regular-finite-table-quantum-classical-hamming-gap`, which includes the
missing identity and regular-character separation errors in both models.
