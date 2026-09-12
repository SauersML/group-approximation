---
rg: 2
id: thin-hnn-regular-selected-profinite-discontinuity-proof
kind: route
title: Britton orthogonality and the profinite tau gap separate the thin stable-letter orbit
target: thin-hnn-regular-selected-module-is-profinite-discontinuous
requires:
  - sln-z-thin-codense-tau-pair
---

The stable letter centralizes `C`, so

```text
v_(xC)=lambda(x) v lambda(x)^*                         (1)
```

is well defined for `xC in A/C`.  If `xC != yC`, Britton normal form says

```text
t^* x^(-1)y t y^(-1)x != 1 in G.                       (2)
```

The canonical group trace therefore gives

```text
<v_(xC),v_(yC)>=delta_(xC,yC).                         (3)
```

Conjugation by `A` permutes this orthonormal frame by left translation,
proving `(THD1)`.  Because `[A:C]=infinity`, this quasiregular representation
has no `A`-fixed vector, while its base-coset vector is fixed by `C`.

On the other hand, `sln-z-thin-codense-tau-pair` supplies a number
`kappa>0` such that the `C`-Laplacian is at least `kappa` on `pi_FD^0`.
That positive lower bound passes to every weakly contained representation.
It cannot pass to `lambda_(A/C)`, where the base-coset vector has zero
`C`-energy.  Hence `(THD2)` follows.
