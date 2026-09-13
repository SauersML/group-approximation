---
rg: 2
id: kms-hard-fp-rf-groups-lie-in-apapa-variety
kind: claim
title: The algorithmically complex finitely presented residually finite groups can be taken in the variety A_p^2 A
distinct_from:
  kms-arbitrarily-hard-fp-rf-groups: that imports the quantitative hardness statement with "solvable of class three" as the only structural information; this records that the groups realizing it are the Minsky-machine groups of their Section 4, which lie in the smaller product variety A_p^2 A.
  fp-rf-apapa-groups-satisfy-boone-higman: that is the open embedding problem for this variety; this is the imported fact that the variety already contains inputs beating every recursive time bound.
artifacts:
  - research/artifacts/bh-complex-wp-apapa-reduction-2026-09-13.md
---

**ESTABLISHED** by literature import. For every recursive membership problem
`X` there are a prime `p` and a finitely presented residually finite group `G`
in the product variety `A_p^2 A` such that

```text
any algorithm deciding the word problem of G in time T
yields an algorithm for X in time C*T(C*n) + C*n + C,          (KMSV1)
```

for a constant `C` depending only on `G` and the finite generating set. Here
`A_p^2 A` is the class of groups with a normal series `1 <= T <= N <= G`, `T`
and `N/T` abelian of exponent `p`, and `G/N` abelian.

`(KMSV1)` is `(KMS1)` of `kms-arbitrarily-hard-fp-rf-groups`, read in the same
sense of "as hard as". The only new content is the variety.

It matters because finitely generated metabelian groups have easy word
problems. So `A_p^2 A` is the first product variety in which a Boone--Higman
theorem for finitely presented residually finite inputs forces hard finitely
presented simple groups (`complex-fp-simple-groups-from-apapa-rf-boone-higman`).

DERIVATION
kms-hard-fp-rf-groups-lie-in-apapa-variety-citation
