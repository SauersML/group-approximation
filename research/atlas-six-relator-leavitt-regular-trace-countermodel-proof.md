---
rg: 2
id: atlas-six-relator-leavitt-regular-trace-countermodel-proof
kind: route
title: Align the two Leavitt charts by a finite-subgroup HNN stable letter
target: atlas-six-relator-phase-lift-has-an-exact-leavitt-tracial-countermodel
requires:
  - atlas-charts-overlap-trivially
  - regular-atlas-linearized-h-coercivity
---

All six displayed words are genuine Leavitt-kernel words, so they evaluate
to the identity in `Q`.  Form the HNN extension

```text
G=<Q,u | u i_1(a) u^-1=i_2(a) for every a in A8>.
```

Both chart maps are injective, so Britton's lemma embeds `Q` into `G`.
Represent `G` in `L(G)` with its canonical trace and put `U=lambda_G(u)`.
Relative to the first chart, the second chart is exactly

```text
U lambda_G(i_1(A8)) U^*=lambda_G(i_2(A8)).            (SLTC2)
```

Thus this is exactly the common-orbit phase model inside the finite von
Neumann algebra `L(G)`, and all six nonlinear defects vanish.

The two marked copies of `H=GL_3(2)` do not agree in `Q`: otherwise their
common nonidentity elements would lie in the intersection of the two marked
`A8` subgroups, contradicting `atlas-charts-overlap-trivially`.  Hence some
standard generator `t` of `H` has nontrivial bridge

```text
b_t=i_2(t)i_1(t)^-1 != 1 in Q.
```

In the canonical trace, HNN normal form gives

```text
||lambda_G(b_t)-1||_2=sqrt(2),                        (SLTC3)
```

and under `(SLTC2)` this is precisely the corresponding covariance defect

```text
||rho(t)U rho(t)^*-U||_2.
```

The finite-dimensional operator inequality underlying
`regular-atlas-linearized-h-coercivity` is a positive operator inequality in
the finite-dimensional group algebra of `A8`: the regular representation is
faithful on that algebra.  It therefore holds in every unitary
representation of `A8`, including the conjugation representation on
`L^2(L(G))`.  Applying it to the vector `U` shows

```text
0 < sum_t ||rho(t)U rho(t)^*-U||_2^2
  <= C_lin sum_j l_j(U)^2.
```

This proves `(SLTC1)`.
