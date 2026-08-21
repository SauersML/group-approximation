---
rg: 2
id: sign-double-cosets-separate-pauli-clouds
kind: claim
title: Separated sign double cosets force distinct Pauli row and column clouds
distinct_from:
  relative-coset-pauli-incidence-compiler: that assumes distinct cloud cosets and sign separation as separate input clauses; this derives the former from the latter when the tested sign matrix separates rows and columns.
---

Let X and Z logical clouds have addresses lying respectively in left cosets
`g_q H_X` and `h_r H_Z`.  Suppose every tested sign-`b` pair between `q,r`
has occurrence addresses whose relative difference lies in `P_b`, and

```text
H_X P_0 H_Z  intersect  H_X P_1 H_Z = empty.                  (SDC1)
```

If the tested binary sign matrix separates every two X rows and every two Z
columns, then distinct X clouds lie in distinct `H_X` cosets and distinct Z
clouds lie in distinct `H_Z` cosets.

In particular, for a nondegenerate Pauli/Weyl pairing the cloud-injectivity
clauses of the relative-coset compiler follow from sign-double-coset
separation; they do not require a second ambient convexity theorem.

