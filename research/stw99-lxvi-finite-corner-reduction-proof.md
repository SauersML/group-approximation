---
rg: 2
id: stw99-lxvi-finite-corner-reduction-proof
kind: route
title: Cut down by a finite dyadic corner and stop at the first infinite matrix amplification
target: stw99-lxvi-iff-finite-car-corner-with-infinite-double
requires: []
---

Write `D=M_(2^infinity)` and use its standard increasing matrix algebras
`D_n=M_(2^n)`.

Suppose first that `phi:D->B` solves Problem LXVI, and choose a nonzero
projection `p in D` for which `phi(p)` is finite.  Every projection in an AF
algebra is Murray--von Neumann equivalent to a projection in a finite stage:
approximate it within norm less than one by a finite-stage self-adjoint,
cut the approximation at `1/2`, and use the standard close-projections
unitary.  Hence, after moving `p` within `D`, it is a rank-`r` projection in
some `D_n`.  A rank-one subprojection `e` of `p` has finite image, because a
subprojection of a finite projection is finite.

The matrix units of `phi(D_n)` identify

```text
B ~= M_(2^n)(A),                 A=phi(e) B phi(e).
```

Here `A` is simple and unital, its unit `phi(e)` is finite, and the tail
corner

```text
e D e ~= M_(2^infinity)
```

embeds unitally in `A`.  Since `B` is infinite, `M_(2^n)(A)` is infinite.
Choose the least `m>=1` for which `M_(2^m)(A)` is infinite and put

```text
C=M_(2^(m-1))(A).
```

Then `C` is simple with finite unit, `M_2(C)` has infinite unit, and `C`
contains a unital CAR algebra because
`M_(2^(m-1)) tensor M_(2^infinity) ~= M_(2^infinity)`.  This proves (2).

Conversely, suppose (2), with `psi:D->A`, and put `B=M_2(A)`.  Then `B` is
simple and infinite.  Under a fixed unital isomorphism

```text
D ~= M_2 tensor D,
```

the map `id_(M_2) tensor psi` is a unital embedding `D->B`.  The image of a
rank-one first-factor projection is `e_11 tensor 1_A`, which is finite since
it is Murray--von Neumann equivalent to the finite projection `1_A`.
Therefore this embedding solves Problem LXVI.

