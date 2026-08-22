---
rg: 2
id: leavitt-d4-length12-branch-b-short-packet-fence-proof
kind: route
title: Exhaust branch B with algebraic inverse pairs in the faithful chart
target: leavitt-d4-length12-branch-b-short-packet-fence
requires:
  - leavitt-bergman-adjoint-is-not-unit-inverse
---

For free parameters `(r,s,a,b,c,d)`, put `p=dr` and

```text
H=b_0c_1d_2a_3,               B0=a_0b_1c_2d_3,
B1=r^-1_0a_1b_2c_3,           E1=1,
E4=p^-1s^-1_0 r^-1_1a_2b_3,  E5=c_0p_1s_0.
```

The eliminated boundary is

```text
K=H^-1 B0 H^-1 B1 H^-1 E5^-1 H E4^-1 H.
```

`research/artifacts/search-degree4-length12-branch-b.py` carries every
unit with its algebraic inverse and accepts any nonidentity one-copy mark in
any copy.  MSI array `16672719` exhausted all

```text
12^6 = 2,985,984
```

assignments from `{1,h,u,v,v^-1,a,b,c,d,r,p,e}`.  Exactly 12,388 had one
nontrivial copy projection; none had a full one-copy free-product normal
form.  This is a bounded packet fence, not a universal algebraic fence.

