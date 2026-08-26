---
rg: 2
id: external-return-singer-groupoid-gauge-proof
kind: route
title: Decompose the external return on the source and transport its gauge through one Singer arrow
target: one-singer-square-does-not-identify-external-return-gauge
requires:
  - signed-hecke-normalizer-has-eight-external-root-returns
  - literal-whiteheads-give-gauged-moving-bridge-table
---

Because `lambda_0` is one-dimensional, the `lambda_0`-isotypic carrier is
one fixed label line tensored with its multiplicity space.  The external
normalizer `n=x_78(1)` preserves `lambda_0`, so its restriction is a fixed
scalar label implementer tensored with an involution `E`.  Absorb the
scalar sign into `E`.  The literal Whitehead carries this source line to
the corresponding target line and has restriction `N_J tensor D` for a
fixed label transporter `N_J` and multiplicity unitary `D`.

Conjugation defines the target normalizer `n'=JnJ^(-1)`.  Therefore

```text
(N_J tensor D)(N_n tensor E)
 = (N_(n') tensor E')(N_J tensor D).                  (1)
```

The label equality is fixed by the definition of `n'`; cancelling it in
`(1)` gives

```text
DE=E'D,
E'=DED^(-1).                                          (2)
```

Conversely, for arbitrary multiplicity unitaries `D,E`, defining `E'` by
`(2)` produces an exact representation of this two-object transport
groupoid.  If `D,E` are involutions, so is `E'`.  Hence `(2)` is the
complete multiplicity content of one Singer square.

Take `D=Z tensor I` and `E=I tensor Z`.  They commute, so `E'=E`.  With
normalized matrix trace,

```text
||E-D||_2^2
 =tau((E-D)^*(E-D))
 =2-2tau(ED)=2,                                       (3)
```

because `tau(ED)=tau(Z)tau(Z)=0`.  This supplies an exact zero-defect model
of the square with a fixed positive gauge mismatch.

Replacing `J` by `t=Jv`, where `v` reduces the source, only replaces `D`
by the product of `D` with the source-chart gauge of `v`.  Equation `(2)`
remains conjugacy transport by that product.  Thus one Singer move cannot
turn the external gauge into the Whitehead gauge without another closed
mixed relation.

