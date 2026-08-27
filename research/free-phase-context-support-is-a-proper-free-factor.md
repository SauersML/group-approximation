---
rg: 2
id: free-phase-context-support-is-a-proper-free-factor
kind: claim
title: Every one-cell free-phase context block is supported on a rank-D-minus-one free factor
artifacts:
  - experiments/signed_hecke_one_marginal_escape.py
  - research/artifacts/signed-hecke-common-type-normalization-2026-08-20.md
distinct_from:
  one-binary-marginal-block-escape: that proves selected projections leave the finite root block; this identifies the exact proper infinite subgroup of the free-phase factor containing the entire escaped matrix block.
  infinite-edge-common-commutant-for-first-chord: that asks for a group extension transporting relative spectral pieces; this supplies the first natural proper infinite associated subgroup to test.
---

In `(OBM3)`, put

```text
a_1=1,                 a_i=h_i h_1^(-1),  2<=i<=D,
L_D=<a_2,...,a_D><=F_D.                                  (FPS1)
```

Then `L_D` is a free factor of rank `D-1`, since

```text
{h_1,h_2h_1^(-1),...,h_Dh_1^(-1)}                       (FPS2)
```

is a Nielsen basis of `F_D`.  For every root matrix `f=sum_(i,j)f_(ij)E_(ij)`,

```text
W f W^*=sum_(i,j) f_(ij) E_(ij) h_i h_j^(-1)
       =sum_(i,j) f_(ij) E_(ij) a_i a_j^(-1).            (FPS3)
```

Consequently the whole escaped context matrix algebra

```text
W M_D(C) W^* <= q C[K times L_D] q                     (FPS4)
```

is supported on the proper infinite subgroup `K times L_D`, not on the
entire `K times F_D`.  Whenever `f` has a nonzero off-diagonal coefficient,
`(FPS3)` has a nontrivial `L_D` coefficient, so the corresponding projection
really uses that infinite support and is not in the root block.

At every join-tree attachment the same statement holds relative to the
transported parent matrix units: the new context uses the previous support
group times `L_D` and never needs the complementary free generator `h_1`.
