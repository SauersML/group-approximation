---
rg: 2
id: ec-group-finite-table-realization-proof
kind: route
title: Write the table as a constant-free existential system, solve it in the free product, and pull the solution back
target: existentially-closed-groups-contain-every-finite-table
requires: []
---

Take unknowns `v_t` for `t in S_F`, and the finite system `Sigma` with no
constants:

```text
v_x v_y = v_(xy)        for all x, y in F;
v_s != v_t              for all s != t in S_F.
```

Since `1 in F`, the equation `v_1 v_1 = v_1` is in `Sigma`, and it forces
`v_1 = 1` in any group.

**A solution exists over `H`.**  Put `K = H * G`, the free product, which
contains `H`.  Setting `v_t = t` (the copy of `t` in the free factor `G`)
solves `Sigma` in `K`: the equations hold in `G <= K`, and distinct elements
of `G` stay distinct in `K`.

**Item 1.**  `H` is existentially closed, so `Sigma` has a solution
`(h_t)` in `H`.  Put `psi(t) = h_t`.
- The inequations make `psi` injective.
- The equations give `psi(xy) = psi(x) psi(y)` for `x, y in F`, and
  `psi(1) = 1`.

The table of `psi(F)` in `H` lives on `psi(F) u psi(F)psi(F)`, which is
`psi(S_F)`.  So `psi` is a bijection `S_F -> psi(S_F)` that preserves `1` and
carries the partial operation on `F x F` to the one on `psi(F) x psi(F)`.
That is an isomorphism `tab_G(F) -> tab_H(psi(F))`.

**Item 2.**  If `H` and `G` are torsion-free, so is `K = H * G`: every
element of finite order in a free product is conjugate into a factor (Kurosh
subgroup theorem, or the normal form theorem for free products).  So `K` is a
torsion-free overgroup of `H` in which `Sigma` is solvable.  Since `H` is
existentially closed among torsion-free groups, `Sigma` has a solution in
`H`, and the rest is as in item 1.
