---
rg: 2
id: elementary-root-kernel-equals-level
kind: claim
title: Every elementary root has exactly the level ideal as its kernel in a normal quotient
distinct_from:
  ck-envelope-level-ideal-screen: that proves the common level is a proper core-separating ideal in the CK setting; this identifies each individual root kernel with the common level for every unital ring.
  relative-elementary-fng-iff-level-ideal-fg: that compares finite generation of an ideal with finite normal generation of its relative elementary subgroup; this identifies only intersections of an arbitrary normal subgroup with individual root groups.
artifacts:
  - research/artifacts/ck-quotient-and-cover-bi-index-obstruction-2026-09-08.md
---

Let `U` be a unital associative ring, `n>=3`, `Gamma=EL_n(U)`, and
`N` a normal subgroup of `Gamma`. Define

```text
I=lev(N)={a in U : e_ij(a) in N for every i!=j}.
```

For every fixed `i!=j`,

```text
{a in U : e_ij(a) in N}=I.
```

Consequently the image of each root group in `Gamma/N` is canonically
isomorphic, as an additive group, to `U/I`.

This does not identify `N` with the relative elementary subgroup at level
`I`, nor with a congruence kernel. It asserts no finite generation.

DERIVATION
[[elementary-root-kernel-equals-level-proof]]
