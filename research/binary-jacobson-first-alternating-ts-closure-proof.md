---
rg: 2
id: binary-jacobson-first-alternating-ts-closure-proof
kind: route
title: Recover T and S in compatible roots and reduce the resulting word in the Bass-Serre normal form
target: binary-jacobson-first-alternating-ts-closure-relation
requires:
  - binary-jacobson-one-step-finite-type-envelope-is-marked-mf
  - binary-jacobson-active-cycle-generates-rank-three
  - binary-jacobson-first-mixed-kernel-is-three-syllable
---

The active-cycle calculation gives

```text
h z h=x_13(S),
h A h=q x_23(T),
h q h=q.                                                 (1)
```

Since `c=qA` and all same-position root elements commute, `(1)` implies

```text
h c h=q(qx_23(T))=x_23(T).                               (2)
```

Apply the Steinberg commutator relation twice:

```text
[x_23(T),x_31(1)]=x_21(T),
[x_21(T),x_13(S)]=x_23(TS)=x_23(1)=z.                   (3)
```

This proves `(JAR2)--(JAR3)` in `E`.

It remains to show that the word is not already imposed by the one-step
amalgam.  In `Gamma_F`, the elements `h,c,k,z` are involutions.  With
`t=hch`, `s=hzh`, expand

```text
W=[ [t,k],s ]z
 =h c h k h c h k h z h k h c h k h (c z) h z.         (4)
```

Here the only cancellation in the unreduced commutator expansion is the
adjacent pair of `h` syllables immediately before the last copy of `s`.

Every displayed interior `F`-syllable in `(4)` lies outside
`K=F cap hFh`.  Indeed

```text
h c h=x_23(T),
h z h=x_13(S),
h k h=x_31(Q)x_32(S),
h(cz)h=x_23(T)x_13(S).                                  (5)
```

Apply the Laurent symbol map `J -> F_2[z,z^(-1)]`.  Elements of `F` have
constant symbols, whereas the four right sides of `(5)` respectively have
a `z^(-1)`, a `z`, a `z` in the `(3,2)` entry, and both a `z^(-1)` and a
`z` entry.  None belongs to `F`.  Thus `c,z,k,cz` are outside `K`.

Formula `(4)` is consequently a nonempty reduced Bass--Serre word,
alternating between `h in B\K` and the listed elements of `F\K` (with harmless
endpoint syllables).  It is nontrivial in `Gamma_F`, which proves `(JAR4)`.

Finally `(JAR5)` follows directly from root positions and coefficients.
The root `u=x_21(T)` commutes with `x_23(1)` (same source row), with
`x_43(1)`, and with `x_14(Q)` because `TQ=0`.  On the other hand

```text
[x_21(T),x_14(SQ)]=x_24(TSQ)=x_24(Q),                   (6)
```

using `TS=1`.  The first row of `(JAR5)` is the second identity of `(3)`.
