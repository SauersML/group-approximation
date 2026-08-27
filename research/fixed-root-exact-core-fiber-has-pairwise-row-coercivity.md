---
rg: 2
id: fixed-root-exact-core-fiber-has-pairwise-row-coercivity
kind: claim
title: A fixed-root exact-core fiber has global pairwise row coercivity
distinct_from:
  optimized-core-one-sided-normal-slice-is-exactly-coercive: that assumes one implementer completes the fixed involution to an exact endpoint and obtains an equality; this compares two arbitrary exact implementers even when neither hybrid tuple is exact.
  same-core-involution-cubic-gauge-coercivity: that changes the extending involution over one core; this changes the exact BS implementer under one fixed involution and root.
  uniform-gauge-optimized-induced-energy: that must also select the root stratum and control induced section energy; this proves that the implementer coordinate has no separate nonlinear basin problem once `X,T` are fixed.
---

Let `X` be an involution and let

```text
b_i=(R_i,T),                  i=0,1,                  (FRC1)
```

be any two exact level-`N` BS cores with the same root.  Define their two
moving square-free row values by

```text
W_i=(XR_i)^2,                 V_i=(XT^2R_i)^3.        (FRC2)
```

Then the following global pairwise estimate holds:

```text
||R_1-R_0||_2
 <=||V_1-W_1||_2+||V_0-W_0||_2.                      (FRC3)
```

In particular, if

```text
e_i=||W_i-1||_2^2+||V_i-1||_2^2,
```

then

```text
||R_1-R_0||_2^2<=4(e_0+e_1).                         (FRC4)
```

There is no smallness, operator-norm, rank, or torsion-multiplicity
hypothesis.  Thus for fixed `(X,T)`, all exact implementers whose inversion
and second-cubic rows are small form one normalized-HS cluster with a
universal linear modulus.  Any UGO basin failure must already involve the
root/endpoint coordinate; it cannot be caused by separated row-tame wells
inside one implementer fiber.

There is an immediate same-stratum corollary.  Let `(R_i,T_i)` be exact
cores under the same involution `X`, suppose `T_0,T_1` have the same
multiplicity vector, and assume one root alignment can be chosen inside the
involution commutant:

```text
zX=Xz,                     T_1=zT_0z^*.               (FRC5)
```

Writing

```text
e_i=||(XR_i)^2-1||_2^2+||(XT_i^2R_i)^3-1||_2^2,
```

one then has

```text
||R_1-zR_0z^*||_2^2<=4(e_0+e_1).                     (FRC6)
```

Thus after an `X`-central root alignment, every remaining exact-core
coordinate is already globally controlled.  The unresolved within-stratum
geometry is precisely construction of that joint `X`/root alignment (or an
adaptive exact endpoint orbit replacing it).
