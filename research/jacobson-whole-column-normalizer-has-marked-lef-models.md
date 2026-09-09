---
rg: 2
id: jacobson-whole-column-normalizer-has-marked-lef-models
kind: claim
title: The whole-column normalizer cover is finitely generated and MF but its exact finite-dimensional representations kill the head
distinct_from:
  finite-root-algebra-forces-steinberg-triviality: that proves exact finite-dimensional collapse from root algebra; this constructs a genuine finitely generated LEF group where exact finite-dimensional collapse holds but MF collapse fails.
artifacts:
  - research/artifacts/jacobson-whole-column-normalizer-has-marked-lef-models-2026-09-08.md
---

Let `J=F_2<S,T | TS=1>`, `Q=1-ST`, and `I=JQJ`. Put

```text
H_col=(J,+)^2 semidirect (GL_2(F_2) * <eta | eta^2=1>),
eta(a,b)=(Qa+Sb,Ta),
```

with the standard constant action of `GL_2(F_2)`. Then `H_col` is
finitely generated and LEF, hence MF, and

```text
Res_fin(H_col)=Res_fd(H_col)=I directSum I <= (J,+)^2.
```

In particular the mark `(Q,0)` survives finite local models at norm
distance `2` while every exact finite-dimensional representation kills
it. The group is not residually finite and is not finitely presented.

The artifact proves the more general finite linear extension theorem:
an elementary abelian `2`-group acted on by a free product of finite
groups and a finitely generated free group has LEF semidirect product.

This is a proper cover of the literal column normalizer. If
`u=x_12(1), v=x_21(1)` in the constant actor, then
`r=[u,eta v eta]` has infinite order in the abstract free product,
while its literal image is the nonidentity involution `x_12(SQ)`.
Thus the models omit the specific actor relation `r^2=1`, as well
as the full three-row packet. They do not refute the coherent matrix gap.

DERIVATION
jacobson-finite-linear-extension-models-proof
