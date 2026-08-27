---
rg: 2
id: spherical-one-shared-map-relation-extension-proof
kind: route
title: Match one new colour tightly and define the other by composition
target: spherical-one-shared-map-relation-extension
requires:
  - spherical-tight-single-colour-near-perfect-matching
---

Treat first the case that `sigma_h` is already chosen and satisfies

```text
||U_h x_i-x_(sigma_h(i))|| <= e.
```

Use `spherical-tight-single-colour-near-perfect-matching` to choose a
radius-`rho` partial bijection `sigma_k` on `1-o(1)` of the vertices.  Since

```text
E_x ||(U_gU_h-U_k)x||^2 = ||U_gU_h-U_k||_2^2 -> 0,
```

all but `o(N)` sampled roots also satisfy

```text
||(U_gU_h-U_k)x_i|| <= rho.
```

Restrict to roots lying simultaneously in the two partial domains and this
good set.  Define, on the image of this restricted `sigma_h`,

```text
sigma_g(sigma_h(i)) = sigma_k(i).
```

This is a partial bijection because both `sigma_h` and `sigma_k` are
injective.  The relation is true by definition.  Its geometric error is

```text
||U_g x_(sigma_h(i))-x_(sigma_g(sigma_h(i)))||
 <= ||U_g x_(sigma_h(i))-U_gU_h x_i||
    + ||(U_gU_h-U_k)x_i||
    + ||U_kx_i-x_(sigma_k(i))||
 <= e+2rho.
```

If `sigma_k` is the old map, choose `sigma_h` tightly and use the identical
definition of `sigma_g`; the same triangle inequality applies with `e` on
the `k` term.  If `sigma_g` is the old map, choose `sigma_k` tightly and put

```text
sigma_h(i)=sigma_g^(-1)(sigma_k(i))
```

whenever the right side lies in the range of the old partial bijection.
Only `o(N)` roots are lost because both old domain/range complements are
`o(N)`.  Applying `U_g^*` to the same three-term comparison gives the bound
`e+2rho` for the new `h` map.  This proves all orientations.
