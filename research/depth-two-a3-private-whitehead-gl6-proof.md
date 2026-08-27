---
rg: 2
id: depth-two-a3-private-whitehead-gl6-proof
kind: route
title: Realize the marked A3 path and three private rank-two Weyl cells in GL6
target: depth-two-a3-private-whiteheads-have-finite-gl6-model
requires:
  - depth-two-a3-return-is-gauged-external-root
  - private-arm-opposite-cell-has-finite-m3-model
  - native-weyl-return-gauges-have-s3-model
---

Prefix cancellation gives `(APW3)`.  Thus the words `(APW4)` are genuine
partial Whiteheads in the original elementary Leavitt group, not formal
opposite labels.

For the finite occurrence model use `x_ij=I+E_ij` over `F_2`.  The ordinary
Steinberg multiplication rule gives

```text
[x_12,x_23]=x_13,          [x_13,x_36]=x_16,
[x_23,x_36]=x_26,          [x_12,x_26]=x_16,
[x_36,x_65]=x_35,          [x_35,x_56]=x_36.
```

This proves both bracketings and the nonzero `G`-opposite return in
`(APW5)`.  The root `x_56` commutes with `x_12,x_23,x_36`, proving the
cross-zero and incidence rows while remaining nonidentity.

For any pair `x_ij,x_ji`, direct two-by-two multiplication in
characteristic two shows

```text
w=x_ij x_ji x_ij,        w^2=1,
w x_ij w^(-1)=x_ji,      w x_ji w^(-1)=x_ij.
```

Apply this calculation to `(1,2)`, `(2,3)`, `(5,6)`, and optionally
`(1,6)`.  It proves every row in `(APW7)` and the output analogue.  Since
`x_16` has a nonzero off-diagonal entry, `(APW8)` follows.

The executable artifact repeats these calculations as exact six-bit-row
matrix arithmetic on MSI.  It verifies both nested commutators, every
displayed zero-incidence row, all four involution and conjugation tables,
and nontriviality of the mark.  The finite-group regular representation
then proves `(APW9)`.
