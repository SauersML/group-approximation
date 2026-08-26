---
rg: 2
id: authenticated-mixed-loop-kills-minuscule-affine-modules
kind: claim
title: The authenticated mixed loop kills the entire minuscule affine Serre sector
artifacts:
  - research/authenticated-mixed-loop-minuscule-module-proof.md
distinct_from:
  authenticated-mixed-loop-kills-natural-affine-gauges: that treats direct sums of the defining module; this also treats the contragredient module, trivial modules, every Frobenius twist of these, and arbitrary iterated extensions among them.
  rank-one-closure-excludes-noncentral-outlier-gauges: that quantifies over arbitrary unitary or nonlinear gauges and noncongruence actors; this remains a defining-characteristic linear theorem for a specified Serre subcategory and does not claim the universal group-ring Bezout identity.
---

Let `k` be a finite field of odd characteristic, let `K/k` be any field
extension, and put

```text
F=SL_3(k),                    M=K^3.                    (MAM1)
```

For `j>=0`, let `M^(j)` denote the `j`th Frobenius twist of the defining
module, and let `(M^*)^(j)` be its contragredient.  Let `S_min` be the full
subcategory of finite-dimensional `KF`-modules whose composition factors
belong to

```text
K_triv,             M^(j),             (M^*)^(j).      (MAM2)
```

Use the honest coefficient copy of `F` and lift

```text
h=diag(2,1,1/2)
```

to `(lambda,h)` in `V rtimes F`, where `V` is any module in `S_min`.
If the unbalanced torus word and the authenticated mixed denominator word

```text
R_tor=1,
[(lambda,h)x_21(-1)(lambda,h)^(-1),x_13(1)]
  =(lambda,h)^(-1)x_23(-1)(lambda,h)                  (MAM3)
```

hold, then

```text
lambda=0.                                               (MAM4)
```

This strictly enlarges the known natural-module sector.  In particular it
allows arbitrary nonsplit extensions and arbitrary multiplicities of the
modules in `(MAM2)`; semisimplicity is not assumed.

The boundary is exact.  On a completely arbitrary `KF`-module the two
relations are the two group-algebra rows `X,Y` displayed in the proof below.
The universal assertion would say that `X,Y` generate the unit left ideal
of `KF` (with the side changed under the opposite module convention).  No
such Bezout identity is proved here.  Thus modules with other highest
weights, and arbitrary nonlinear/unitary multiplicity gauges, remain in the
frontier.

DERIVATION
authenticated-mixed-loop-minuscule-module-proof
