---
rg: 2
id: authenticated-mixed-loop-kills-quadratic-affine-modules
kind: claim
title: The authenticated mixed loop kills quadratic defining-module gauges
artifacts:
  - research/authenticated-mixed-loop-quadratic-module-proof.md
distinct_from:
  authenticated-mixed-loop-kills-minuscule-affine-modules: that treats the extension closure of degree-zero and the two degree-one minuscule modules; this adds both symmetric squares and hence both pure tensor squares in odd characteristic.
  rank-one-closure-excludes-noncentral-outlier-gauges: that asks for arbitrary unitary or nonlinear gauges and noncongruence actors; this is still an exact defining-characteristic polynomial-module calculation.
---

Use the field and honest coefficient actor of
`authenticated-mixed-loop-kills-minuscule-affine-modules`.  The two affine
Fox rows have zero common kernel on

```text
Sym^2(K^3),                    Sym^2((K^3)^*).           (QAM1)
```

and on every Frobenius twist of `(QAM1)`.  Since the characteristic is odd,

```text
K^3 tensor K^3 = Sym^2(K^3) directSum wedge^2(K^3),
wedge^2(K^3) ~= (K^3)^*,                                (QAM2)
```

and the dual identities hold with `K^3` and `(K^3)^*` exchanged.  Hence the
rows have zero common kernel on both pure tensor squares.  Together with the
mixed-tensor computation in
`authenticated-mixed-loop-kills-bilinear-affine-modules`, this covers every
tensor product of two copies chosen from `K^3` and `(K^3)^*`.  The same is
true for every module admitting a finite filtration whose sections are
trivial, defining, contragredient, either symmetric-square module, or
Frobenius twists of these.

Thus neither nonsplit extension data nor the first nonlinear polynomial
coefficient block supplies the residual affine enemy.  This is not an
arbitrary-highest-weight theorem: the universal two-row group-algebra ideal
remains open.

DERIVATION
authenticated-mixed-loop-quadratic-module-proof
