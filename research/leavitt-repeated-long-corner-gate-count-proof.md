---
rg: 2
id: leavitt-repeated-long-corner-gate-count-proof
kind: route
title: Count immutable gate syllables in the three long corners
target: leavitt-repeated-long-corner-gate-count-obstruction
requires:
  - leavitt-repeated-long-corner-template-kills-omega
---

Write

```text
x=g_0,  y=g_1,  u=g_4,  v=g_7.
```

The three long corners, displayed with their coefficient-copy indices, are

```text
H=x_0|y_1|a_2|c_1|u_2|b_3|d_2|v_3,
L=v_0|x_1|y_2|a_3|c_2|u_3,
N=u_0|b_1|d_0|v_1|x_2|y_3.                         (GC1)
```

Delete any of `x,y,u,v` which equals the identity.  In each line of `(GC1)`
all remaining adjacent copy indices are still different: the four fixed
gates separate every potentially matching pair.  Thus no two displayed
syllables merge and no internal group identity beyond a variable being the
identity can shorten a corner.

Let `k` be the number of nonidentity elements among `x,y,u,v`.  Since
`a,b,c,d` are nonidentity, reduced free-product normal form gives

```text
ell_C(H)=4+k,        ell_C(L)=ell_C(N)=2+k.          (GC2)
```

Equality of elements in a free product implies equality of their reduced
syllable lengths.  Equation `(GC2)` therefore excludes `H=L` and `H=N` for
arbitrary choices in the coefficient group.

As a bounded independent check, the faithful-Bergman artifact enumerated all
82 distinct packet elements represented by canonical words of radius at most
two in each of the four free slots.  Its sixteen MSI shards tested
`82^4=45,212,176` layouts and found zero collisions, in agreement with the
general proof.
