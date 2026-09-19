---
rg: 2
id: binary-jacobson-positive-tail-literalization-proof
kind: route
title: Conjugate the three surviving folded rows by the balanced shift matrix
target: binary-jacobson-positive-tail-fold-is-a-literal-degree-two-tuple
requires:
  - binary-jacobson-tail-phase-cannot-correct-closing-fold
  - binary-jacobson-naive-head-polar-is-balanced-return
---

The support calculation for the balanced polar gives

```text
R=aE_-,
```

because `R=R E_-` and `aE_-` has range in `F<=P`.  The operators
`bX_0,X_1,Z_1` preserve `E_-`.  Hence the folded formulas from the
prerequisite become conjugations by the literal matrix `a`:

```text
T X_0T^*=F_+ a(bX_0)a^(-1)F_+,
T X_1T^*=F_+ aX_1a^(-1)F_+,
T Z_1T^*=F_+ aZ_1a^(-1)F_+.                            (1)
```

Now

```text
bX_0=x_12(1+Q)=x_12(ST).                                (2)
```

Using

```text
a=[[S,Q],[0,T]],        a^(-1)=[[T,0],[Q,S]]            (3)
```

on rows `1,2`, direct multiplication gives

```text
a x_12(ST)a^(-1)=x_12(S^2).                             (4)
```

Conjugating a column root with target `4` multiplies its coefficient column
by `a`, so

```text
a x_14(Q)a^(-1)=x_14(SQ).                               (5)
```

The root `x_43(1)` uses neither active row and commutes with `a`.  Together
with the already proved equality `TZ_0T^*=0` on `F_+`, equations `(1)--(5)`
prove `(JLT1)`.

The range `F_+` is the joint spectral cut obtained by conjugating the cuts
for `x_13(Q),x_23(Q),x_13(ST)` by `a`.  Their conjugates are same-position
roots, including `x_13(Q)` and `x_13(SQ)`, so all words in `(JLT1)--(JLT2)`
reduce `F_+`.  The commutator

```text
[x_14(SQ),x_43(1)]=x_13(SQ)                             (6)
```

acts as `-1` there, while `x_12(S^2)` cross-commutes with this pair.  This
proves the degree-two assertion.  The native two-qubit theorem applied to
the same nonzero reducing subprojection proves the degree-four assertion.
