---
rg: 2
id: stw87-diagonal-bimodular-localization-no-go-proof
kind: route
title: Singleton diagonal corners force uniqueness of the expectation through every normalized Schur localization
target: stw87-diagonal-bimodular-localization-no-go
requires:
  - stw87-diagonal-expectation-order-zero-obstruction
  - stw87-diagonal-order-zero-maps-annihilate-matrix-colours
artifacts:
  - research/artifacts/stw87-diagonal-bimodular-localization-no-go-audit-2026-08-30.md
---

For `x in X`, write `p_x` for the singleton projection in `D`.  Suppose
that `R:A->D` is a bounded `D`-bimodule map and `R|_D=id_D`.  For every
`a in A`, bimodularity gives

```text
p_x R(a) p_x = R(p_x a p_x)=a_(xx) p_x.
```

Since an element of `D` is determined by its singleton corners, this says
`R(a)=E_X(a)` for every `a`.  Thus `R=E_X`; positivity and complete
positivity are not needed for uniqueness.

Now let `S:A->A` be bounded, `D`-bimodular, and the identity on `D`.
The composite `E_X S:A->D` is again a bounded `D`-bimodule map and is the
identity on `D`.  The uniqueness just proved yields

```text
E_X S=E_X.                                             (1)
```

A normalized positive-definite kernel `k:X times X->C`, with
`k(x,x)=1`, defines a c.p.c. Schur multiplier

```text
S_k([a_(xy)])=[k(x,y)a_(xy)].
```

It is `D`-bimodular and fixes `D`, so `(1)` applies.  In particular this
applies when `k` has controlled support, as in the standard property-A
finite-propagation localization.

Let `phi:C^2->A` be the two-point *-homomorphism in
`stw87-diagonal-expectation-order-zero-obstruction`.  Equation `(1)` gives

```text
E_X S phi=E_X phi.
```

The cited claim therefore computes the distance from `E_X S phi` to the
diagonal c.p.c. order-zero maps as exactly `1/2`.  Likewise, for a canonical
matrix-corner inclusion `iota:M_n->A`, `n>=2`, equation `(1)` and
`stw87-diagonal-order-zero-maps-annihilate-matrix-colours` give

```text
inf_theta norm(theta-E_X S iota)=1,
```

where `theta` ranges over diagonal c.p.c. order-zero maps.  Hence making a
nuclear-dimension return map controlled by normalized Schur localization
before applying the diagonal expectation does not change either obstruction.
