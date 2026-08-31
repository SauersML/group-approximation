---
rg: 2
id: quasiregular-fixed-coset-produces-a-false-intertwiner-proof
kind: route
title: A K-fixed coset direction is invisible to the full carrier
target: constant-core-gap-stops-at-k-intertwiners
requires:
  - two-sheet-projective-closure-forces-equivalent-carriers
---

On the Hilbert space `Hom(H_1,H_0)` with its Hilbert--Schmidt inner
product, define the unitary `K`-action

```text
R(k)T=pi_0(k)Tpi_1(k)^*.
```

Its averaging projection is

```text
P_KT=|K|^(-1) sum_(k in K)R(k)T.
```

The fixed space is exactly `Hom_K(H_1,H_0)`. Orthogonal projection and
unitary invariance give

```text
(1/|K|)sum_k||R(k)T-T||_(HS)^2
 =2||T||_(HS)^2-2||P_KT||_(HS)^2
 =2||T-P_KT||_(HS)^2.                                  (QFC1)
```

Multiplication on the right by `pi_1(k)` identifies the summand with
`||pi_0(k)T-Tpi_1(k)||_(HS)^2`. This proves `(CCG1)`.
Because `K` is one fixed finite group, its averaging operator has a
positive spectral gap on the complement of its invariant space; any fixed
generating set gives the corresponding dimension-independent generator
version.

Now let `F=F_N`, let `d=[F:K]>1`, and use the left quasi-regular
representation on right cosets:

```text
Pi_1=lambda_(F/K) on ell^2(F/K).
```

The vector `delta_K` at the base coset is fixed by `K`. The normalized
constant vector

```text
xi=d^(-1/2) sum_(gK in F/K) delta_(gK)
```

is fixed by all of `F`. Set

```text
v=(delta_K-d^(-1/2)xi)/sqrt(1-1/d).                    (QFC2)
```

Then `v` is a unit `K`-fixed vector orthogonal to the full
`F`-fixed space, which is the line `C xi`.

Let `Pi_0=1_F^(directSum d)` on `C^d`, choose a unit vector
`e in C^d`, and define the rank-one operator

```text
Tz=<z,v>e.                                              (QFC3)
```

It has Hilbert--Schmidt norm one. Since `v` is `K`-fixed,
`T Pi_1(k)=T=Pi_0(k)T` for every `k`, so `T in Hom_K`. Every
`F`-intertwiner from `Pi_1` to `Pi_0` has each coordinate functional
proportional to `<.,xi>`. Equation `(QFC2)` makes `T` orthogonal to all
of them. Therefore `(CCG3)--(CCG4)` hold.

Decompose `Pi_1` into irreducible `F`-representations. Its full invariant
line accounts for `xi`, while the nonzero vector `v` lies in the
orthogonal sum of nontrivial isotypes. At least one of its irreducible
components is `K`-fixed. Restricting `(QFC3)` to that component gives the
announced false intertwiner between inequivalent full-carrier sectors.

The construction has zero constant-core energy, so no improvement in the
numerical Kazhdan constant of `K` can remove it. Only relations involving
elements outside `K` can distinguish this Hecke direction from a genuine
`F`-intertwiner.
