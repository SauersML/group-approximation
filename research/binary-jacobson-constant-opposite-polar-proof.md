---
rg: 2
id: binary-jacobson-constant-opposite-polar-proof
kind: route
title: Decompose the constant opposite pair into the sign and standard S3 blocks
target: binary-jacobson-constant-opposite-polar-is-finite-s3
requires:
  - binary-jacobson-constant-q-root-envelope-is-finite
---

The constant roots `x_13(1),x_31(1)` are the two elementary transvections in
one `GL_2(F_2)` block.  Their product has order three, proving `(JOP2)`.

Restrict any unitary representation of this finite group to the negative
spectral cut `e` of `A`.  The trivial representation contributes nothing to
`e`.  On the sign representation, both transpositions act as `-1`, so

```text
e k e=-e.                                                (1)
```

On the two-dimensional standard representation, choose the negative
eigenline of `A`.  Two distinct transpositions are reflections whose
negative axes meet at angle `pi/3`; compression of `k` to that line is

```text
e k e=(1/2)e.                                            (2)
```

Equations `(1)--(2)` exhaust the irreducibles of `S_3` on which `e` is
nonzero and prove the polynomial `(JOP3)`.  Its two roots are `-1,1/2`, so
`K` is invertible and its sign is the unique affine polynomial

```text
alpha K+beta e
```

taking the values `-1,+1` on those roots.  Solving gives
`alpha=4/3,beta=1/3`, proving `(JOP4)`.

Finally `x_13(1)=x_13(Q)x_13(ST)`, which gives `(JOP5)`.  Both roots in
`(JOP1)` are constant roots, so the prerequisite places the entire
calculation in its finite marked envelope.  No spectral or polar operation
inside this `S_3` block introduces the raw coefficient `SQ`; this proves the
stated fence.
