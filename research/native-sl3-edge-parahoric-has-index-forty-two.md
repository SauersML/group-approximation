---
rg: 2
id: native-sl3-edge-parahoric-has-index-forty-two
kind: claim
title: The native dyadic SL3 edge parahoric has index forty-two and six explicit Weyl depth profiles
distinct_from:
  native-hecke-edge-rank-integrality-is-bounded: that proves abstract finiteness of the Hecke shells and a bounded clique consequence; this computes the exact stabilizer, its index, and all six root-depth profiles.
  selected-corner-correction-contains-regular-correction: that gives the correction-theoretic no-go for a selected atom; this identifies the precise finite-index group acting on each atom.
---

Put

```text
C=SL_3(Z),
h=diag(2,1,1/2),
D=C cap hCh^-1.                                         (NSP1)
```

Then `D` consists exactly of the matrices `g in C` satisfying

```text
v_2(g_12)>=1,       v_2(g_23)>=1,       v_2(g_13)>=2,  (NSP2)
```

with no extra divisibility condition on the three lower-root entries.  It is
the stabilizer in `C` of

```text
L=4Z e_1 directSum 2Z e_2 directSum Z e_3,              (NSP3)
```

and

```text
[C:D]=42.                                               (NSP4)
```

More generally, for `lambda=(1,0,-1)` and a Weyl permutation `w in S_3`,
write `lambda_w=w lambda` and `D_w=wDw^-1`.  Then

```text
g in D_w
 iff v_2(g_ij)>=max(0,lambda_(w,i)-lambda_(w,j))
     for every i!=j.                                   (NSP5)
```

There are six distinct oriented depth profiles, each of index `42`.  Their
common intersection has

```text
g_ij divisible by 4       for every i!=j,               (NSP6)
```

with only the determinant-one condition on the diagonal entries.

If `P=(1-c)/2` and `Q_w=h_w P h_w^-1` are the native commuting edge
projections, every one of their four joint atoms commutes with `D_w`.
Canonical mixed trace tests give each positive atom the normalized regular
trace of `D_w`.  Weyl conjugation transports the entire quartet for `w` to
the quartet for `vw`; it does not make one quartet invariant under all six
parahorics.
