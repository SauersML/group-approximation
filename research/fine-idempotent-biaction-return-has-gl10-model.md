---
rg: 2
id: fine-idempotent-biaction-return-has-gl10-model
kind: claim
title: The literal fine-idempotent two-sided return still closes in GL10
artifacts:
  - research/fine-idempotent-biaction-return-gl10-proof.md
  - experiments/fine_idempotent_biaction_return_gl10_audit.py
distinct_from:
  row2-parallel-a2-return-diamond-has-gl8-model: that factors and compares the two literal occurrences of a_2=s_1t_00 but does not expose the reverse product b_2a_2=s_00t_00; this adds that fine idempotent and both of its native left/right absorption rows.
  returned-opposite-cross-zero-has-finite-s6-model: that places the two depth-one range idempotents on disjoint Coxeter triples and authenticates their zero product; this uses the depth-two singleton e_00=s_00t_00 and retains the uncancelled Morita factors s_00,t_00 on both sides of it.
  one-sided-leavitt-connector-has-sharp-overlap-payment: that proves the rank/trace payment after the physical support projection for e_00 has been decoded; this shows that literal root wordization of e_00, even with two-sided coefficient action on its defining Morita arms, does not decode that support projection.
---

**ESTABLISHED FINE-SUPPORT FINITE FENCE.**  Put

```text
a_2=s_1t_00,              b_2=s_00t_1,
e_00=b_2a_2=s_00t_00.                                  (FIB1)
```

Retain the coupled `J_1,J_2` prefix packet, both native order-seven heads,
the row-two marked-center return, and both literal `a_2` paths from
`row2-parallel-a2-return-diamond-has-gl8-model`.  In particular it already
contains the actual occurrences

```text
A_2=x_(5,8)(a_2),        B_2=x_(8,6)(b_2),
S_1=x_(5,7)(s_1),        T_00=x_(7,8)(t_00),
[S_1,T_00]=A_2.                                       (FIB2)
```

Factor the other arm natively,

```text
S_00=x_(8,h)(s_00),      T_1=x_(h,6)(t_1),
[S_00,T_1]=B_2.                                       (FIB3)
```

Let `K` be a fixed product of constant Weyl words carrying the ordered
triple `(8,h,6)` to `(v,h,10)`.  Write

```text
bar S_00=K S_00 K^(-1)=x_(v,h)(s_00),
bar T_1 =K T_1  K^(-1)=x_(h,10)(t_1),
bar B_2 =K B_2  K^(-1)=x_(v,10)(b_2).                (FIB4)
```

The reverse product is now a literal ordinary-root commutator on the actual
row-two arm:

```text
D=[bar B_2,A_2]=x_(v,8)(e_00).                       (FIB5)
```

This does more than merely name the coefficient `e_00`.  Let `L=w_(v,8)(1)`
be the constant Whitehead exchanging `v` and `8`.  The same named Morita
arms occur in the two exact absorption rows

```text
[D, L bar S_00 L^(-1)] = bar S_00,
[L T_00 L^(-1), D]     = T_00.                       (FIB6)
```

Indeed `(FIB6)` is precisely the pair of Leavitt identities

```text
e_00 s_00=s_00,             t_00 e_00=t_00.          (FIB7)
```

Thus the table contains the literal fine-idempotent root, its two native
Morita factors, both factorization paths, and left and right action of the
idempotent on those same occurrences.  In particular it contains both local
biaction rows that a physical support interpretation would have to respect;
what it does not contain is a spectral incidence identifying a groupified
reflection with the physical `e_00` corner.

The whole table nevertheless has an exact marked model in `GL_10(F_2)`.
Extend the preceding eight-vertex chart by `v,h`.  Keep all old matrices and
put

```text
S_00=e_(8,h),       T_1=e_(h,6),
K=(8 v)(6 10),
bar S_00=e_(v,h),   bar T_1=e_(h,10),
bar B_2=e_(v,10),   D=e_(v,8),       L=(v 8).         (FIB8)
```

Then `(FIB3)--(FIB6)` are standard length-two transvection and constant
Whitehead identities.  The marked child remains the nonidentity
transvection on the old disjoint pair `(7_1,8_1)`.  Passing to the complex
left regular representation of the finite generated subgroup gives an exact
finite-dimensional unitary occurrence model in which the marked involution
has operator-norm distance two from the identity.

There is also a direct signature mismatch.  The matrix `D` is a nonidentity
involution, so left multiplication by `D` partitions the finite group into
two-cycles.  Hence in the complex regular representation

```text
rank((1-lambda(D))/2)=(1/2)dim(lambda).                (FIB9)
```

The physical minimal corner of a depth-two `4 by 4` packet has rank one
quarter of its carrier.  Thus even the most immediate spectral reading of
the literal `x(e_00)` word gives a half-support reflection, not the required
fine support.

Consequently literal wordization of `x(e_00)` and even both native
two-sided action rows do **not** authenticate

```text
R_P=1-2s_00t_00
```

as the physical fine-corner reflection on the same carrier.  If this finite
table implied the operator-norm row of
`opnorm-leavitt-coarse-fine-return-row`, its zero-defect marked model would
produce a nonzero common `2 by 2`/`4 by 4` carrier with vanishing leakage,
contradicting `rank-deficient-return-row-has-operator-norm-one`.

This is a scoped model of the displayed ordinary-root occurrence table, not
a representation of the full binary Leavitt elementary group.  It leaves a
strictly sharper residue: a successful mixed return must attach the
fine-idempotent occurrence to a **spectral support incidence** on the chosen
carrier (or use coefficient completeness to exclude this `GL_10` type), not
merely prove further multiplication/action identities for `e_00,s_00,t_00`.

No Property T, Kazhdan input, trace hypothesis, literature theorem, local
computation, or Lean compilation is used.

DERIVATION
fine-idempotent-biaction-return-gl10-proof
