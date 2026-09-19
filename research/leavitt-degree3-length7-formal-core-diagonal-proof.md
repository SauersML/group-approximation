---
rg: 2
id: leavitt-degree3-length7-formal-core-diagonal-proof
kind: route
title: Eliminate the two unary relators and read the target as the last diagonal equality
target: leavitt-degree3-length7-formal-core-is-diagonal
requires:
  - leavitt-degree3-length7-formal-core-exists
---

The exact orbit computation gives

```text
R_1 = z x_2,
R_2 = z x_0,
R_0 = z^(-1)x_2 z(x_0x_1)z x_0^(-1)z^(-1)x_2^(-1)z.
```

The first two equations give `z=x_2^(-1)` and `x_0=x_2`; write their common
value as `X`.  Direct substitution into the third gives

```text
R_0 = X^2 x_1 X^(-3).
```

Thus `R_0=1` is equivalent to `x_1=X`.  These are reversible Tietze moves,
so the quotient is `<X>` and, after free-producting every stage with `D`, the
quotient is `D*<X>`.  In particular no nonidentity element of `D` dies.

The same calculation applies to the coefficient family

```text
g_0=g_4=1,  g_5=g_2^(-1),  g_6=g_1^(-1).
```

Its unary corners are `g_{3,2}` and `g_{3,0}`.  After identifying them, the
remaining relation merely conjugates `g_{3,1}` to the common element by a
word in the other coefficients; `g_1` is an outer conjugating decoration.
Hence this whole inverse-pair family is gluing data and cannot by itself
produce the marked `D`-kernel.
