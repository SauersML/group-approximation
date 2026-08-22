---
rg: 2
id: leavitt-d4-l14-n0511-is-fenced-proof
kind: route
title: Embed all five normal branches in the universal branch-I fence
target: leavitt-d4-l14-n0511-is-fenced
requires:
  - leavitt-d4-l14-n0511-branch1-is-fenced
  - leavitt-d4-l14-n0511-first-carrier-splits-five-ways
---

Use the branch-I parameters `(p,d,b,c,u)` and `a=du p^-1` from the exact
nineteen-syllable boundary in the branch-I proof.  Direct substitution in
the raw corners gives the following specialization maps for the other four
maximal branches:

```text
II:  a=w^-1p^-1,  du=w^-1                    (set branch-I y=1);
III: a=y^-1p^-1,  du=y^-1                    (set branch-I w=1);
IV:  a=p^-1,      du=1                       (set branch-I w=y=1);
V:   a=p^-1,      u=d=1                      (set branch-I w=y=u=d=1).
```

In every case the unused coefficients cancel in the raw Reidemeister--
Schreier words, leaving identically

```text
H=c_0d_1p^-1_2b_3,
B0=b_0c_1d_2p^-1_3,
B1=u^-1_0p^-1_1b_2c_3,
E6=a_0b_1c_2d_3,
K=H^-1B0 H^-1B1 H^-1E6.
```

These are precisely specializations of the branch-I boundary enumerated by
the certificate.  That enumeration covers all four possible target copies,
all `12,768` color-compatible noncrossing partitions, and all `180,528`
distinguished-target-block schemes, with no unresolved nontrivial target.
Therefore branches II--V inherit the branch-I fence, and the five branches
exhaust normal class `0;511`.
