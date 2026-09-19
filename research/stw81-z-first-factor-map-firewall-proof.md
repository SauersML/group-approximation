---
rg: 2
id: stw81-z-first-factor-map-firewall-proof
kind: route
title: Globalize Z and isolate the dimension of the first-factor embedding
target: stw81-z-stable-usc-fields-reduce-to-first-factor-map
requires:
  - stw81-finite-base-usc-fibre-product-bound
artifacts:
  - research/artifacts/stw81-z-stable-field-first-factor-firewall-2026-08-30.md
---

Hirshberg--Rordam--Winter,
[*C0(X)-algebras, stability and strongly self-absorbing C-star
algebras*](https://arxiv.org/abs/math/0610344), Theorem 4.6, applies to
arbitrary separable `C_0(X)`-algebras over finite-dimensional locally
compact metrizable `X`.  Since `Z` is K1-injective and strongly
self-absorbing, fibrewise Z-stability gives `(ZFF1)` without field
continuity or local triviality.

Every nonzero fibre is simple, separable, nuclear, non-elementary and
Z-stable.  The unital theorem of
Castillejos--Evington--Tikuisis--White--Winter and its nonunital extension
by Castillejos--Evington give

```text
dim_nuc(A_x)=1.
```

The upper-semicontinuous fibre product bound therefore gives
`dim_nuc(A)<=2dim(X)+1`.  Evaluation onto any nonzero non-AF fibre gives the
lower bound one.

We next prove `(ZFF4)`.  For every star-homomorphism `theta:A->B`, composing
nuclear-dimension approximations of `A` with `theta` gives

```text
dim_nuc(theta)<=dim_nuc(A).                                (ZFP1)
```

Thus `dim_nuc(iota_A)<=dim_nuc(A)`.  Since `A` is Z-stable and `Z` is
strongly self-absorbing, there are isomorphisms

```text
sigma_m:A tensor Z -> A
```

such that `sigma_m(iota_A(a))->a` for every `a in A`.  Composition with an
isomorphism does not increase map dimension, and a point-norm limit of maps
of nuclear dimension at most `d` again has dimension at most `d` by a
diagonal choice of finite-dimensional approximations.  Hence

```text
dim_nuc(A)=dim_nuc(id_A)
 <=dim_nuc(iota_A),                                       (ZFP2)
```

proving equality.

Finally, Tikuisis--Winter,
[*Decomposition rank of Z-stable C-star
algebras*](https://arxiv.org/abs/1210.1386), proves
`dr(C(Y) tensor Z)<=2` for compact Hausdorff `Y`.  Taking `Y=[0,1]` gives
the precise constant-field checkpoint `(ZFF5)--(ZFF6)`.  Their result is a
two-bound, not the one-bound required here.  The simple nuclear-dimension
theorems cannot be applied to `C([0,1]) tensor Z`, which has the full
interval of ideals.
