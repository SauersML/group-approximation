---
rg: 2
id: leavitt-d4-length12-branch-a-short-packet-fence-proof
kind: route
title: Exhaust branch A with algebraic inverse pairs in the faithful chart
target: leavitt-d4-length12-branch-a-short-packet-fence
requires:
  - leavitt-bergman-adjoint-is-not-unit-inverse
---

For branch-A parameters `(x,r,y,a,b,c)`, set `q=x^-1y^-1` and

```text
H=b_0 c_1 q_2 a_3,
B0=a_0 b_1 c_2 x^-1_3,
B1=q_0 a_1 b_2 c_3,
E1=y_3,
E4=r^-1_0 q_1 a_2 b_3,
E5=(cr)_0.
```

The eliminated boundary is

```text
K=H^-1 B0 H^-1 B1 E1^-1 H^-1 E5^-1 H E4^-1 H.
```

`research/artifacts/search-degree4-length12-branch-a.py` carries every
chart element together with its algebraic group inverse and accepts any
nonidentity one-copy mark in any coefficient copy.  MSI array `16671866`
exhausted all

```text
12^6 = 2,985,984
```

assignments from `{1,h,u,v,v^-1,a,b,c,d,r,p,e}`.  Exactly 11,834 had one
nontrivial copy projection; none had a full one-copy free-product normal
form.  This is a bounded packet fence, not a universal algebraic fence for
branch A.

