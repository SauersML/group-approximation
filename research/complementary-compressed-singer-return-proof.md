---
rg: 2
id: complementary-compressed-singer-return-proof
kind: route
title: Separate the two prefix idempotents along a Singer covector orbit
target: complementary-compressed-singer-words-only-return-gauged-head
requires:
  - leavitt-compression-preserves-root-position-support
  - fano-semidir-bridges-are-wrong-subgroup-or-gauged
---

For a constant binary matrix `A`, the two Leavitt compression maps are

```text
alpha_0(A)=qI+s_0At_0=qI+pA,
alpha_1(A)=pI+s_1At_1=pI+qA.                           (1)
```

Since `p,q` are complementary orthogonal idempotents and commute with
constant matrices, multiplication of `(1)` proves `(CCS2)` and induction
proves `(CCS3)`.

Expanding `h d h^(-1)` with `(CCS3)` kills both cross terms because
`pq=qp=0`, giving `(CCS6)`.  In every matrix entry the coefficients of the
two constant binary matrices lie in the four-element span

```text
{0,p,q,p+q}={0,p,q,1}.
```

The elements `p,q` are nonzero and linearly independent over `F_2` because
`p+q=1`.  Therefore an equality

```text
pA+qB=C,                   A,B,C in M_20(F_2),         (2)
```

implies `A=B=C` entrywise.  Under `(CCS4)`, apply `(2)` to `(CCS6)` for
each `d in L_0`.  Both constant conjugates belong to `tL_0t^(-1)`, and the
three groups have the same finite cardinality, proving `(CCS7)`.

It remains to compute a stabilizer without enumeration.  In the directed
root list `(ERN1)`, the set of sources is `{4,5,6,8,9}`.  Hence the common
fixed-vector space of `L_0` is exactly

```text
Fix(L_0)=<e_2,e_7>.                                    (3)
```

For row one, `t` fixes `e_2` and is a Singer cycle on `(4,7,8)`.  Equality
of the fixed spaces in `(CCS7)` implies

```text
<e_2,t^ae_7>=<e_2,t e_7>,                              (4)
```

and similarly for `b`.  The active and fixed coordinate spaces are a
direct sum, while a Singer cycle acts freely on the seven nonzero active
vectors.  Thus `(4)` forces `a=b=1 mod 7`.

For row two use covectors.  The set of targets in `(ERN1)` is
`{2,4,5,7,8}`, so the common fixed-covector space is exactly

```text
Fix(L_0^*)=<e_6^*,e_9^*>.                              (5)
```

The row-two Singer actor fixes `e_6^*` and acts freely on the seven nonzero
covectors of its active `(5,8,9)` block.  The fixed-covector spaces of the
three groups in `(CCS7)` are respectively

```text
<e_6^*,e_9^*t^(-a)>,  <e_6^*,e_9^*t^(-b)>,
<e_6^*,e_9^*t^(-1)>.
```

Their equality forces `a=b=1 mod 7`.  In either row, `(CCS3)` now gives
`h=t`.  Character signs need not be checked because failure to carry the
underlying subgroup already excludes the signed Reynolds transport.
