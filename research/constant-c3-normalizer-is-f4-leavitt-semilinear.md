---
rg: 2
id: constant-c3-normalizer-is-f4-leavitt-semilinear
kind: claim
title: The constant C3 normalizer is the semilinear unit group of the F4 Leavitt algebra
distinct_from:
  z-fixed-support-five-hecke-normal-form: that says one rank-five branch is supported in the normalizer; this computes that normalizer exactly and shows why the branch retains the original Leavitt difficulty.
  leavitt-matrix-amplification-in-unit-group-algebra: that uses the full constant S3 packet commuting with scalar Leavitt units to build matrix corners; this computes the centralizer and normalizer of its C3 subgroup, which is substantially larger than the scalar copy.
  d-ary-leavitt-groups-nonsofic-over-finite-fields: that proves nonsoficity over every finite coefficient field; this algebraically identifies the F4 unit group inside the rank-five normalizer branch.
artifacts:
  - research/artifacts/constant-c3-normalizer-f4-leavitt-2026-08-21.md
---

Let `R=L_(F_2)(1,2)`, identify `R^x` with `GL_2(R)` by binary
self-similarity, and let

```text
r=[[0,1],[1,1]],        H=<r>=C_3
```

be the constant subgroup used by the corner idempotents.  Then

```text
C_(R^x)(H) = (R tensor_(F_2) F_4)^x = L_(F_4)(1,2)^x,
N_(R^x)(H) = L_(F_4)(1,2)^x semidirect Gal(F_4/F_2).
```

The nontrivial Galois element is represented by either constant transposition
in `S_3=GL_2(F_2)` and sends `r` to `r^(-1)`.

Consequently the normalizer-supported half of the minimal rank-five Hecke
normal form is not a finite or amenable residue: it already contains the
binary Leavitt unit group over `F_4`, which is nonsofic.  Excluding a `(5,7)`
corner witness in this branch requires new direct-finiteness information and
does not follow from subgroup trapping.
