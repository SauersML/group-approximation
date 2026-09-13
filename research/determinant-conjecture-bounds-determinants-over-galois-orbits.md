---
rg: 2
id: determinant-conjecture-bounds-determinants-over-galois-orbits
kind: claim
title: The determinant conjecture bounds the product of Fuglede-Kadison determinants of a pencil over a Galois orbit of algebraic points below by minus N times the finite height
distinct_from:
  determinant-conjecture-gives-one-variable-atiyah-base-change: that uses companion models of one polynomial, the one-variable case of this identity; this attaches an integral model to any zero-dimensional cycle in the plane, through multiplication maps on monomial lattices.
artifacts:
  - research/artifacts/atiyah-two-variable-base-change-2026-09-13-part2.md
---

**ESTABLISHED (unreviewed)** by [[determinant-conjecture-galois-orbit-bound-proof]].

Let `G` satisfy Lueck's determinant conjecture. Let
`M(x) = M_0 + x_1 M_1 + x_2 M_2` with `M_i in M_N(Z[G])`. Let `zeta in Qbar^2`
have Galois orbit `sigma_1 zeta, ..., sigma_D zeta`, and suppose every
`M(sigma_j zeta)` is injective. Write
`F_Z = c_Z prod_j (u_0 + u_1 sigma_j zeta_1 + u_2 sigma_j zeta_2)` for the
primitive integral Chow form of the orbit. Then

```text
sum_(j=1..D) log Delta(M(sigma_j zeta))  >=  - N log |c_Z|,
```

and `log |c_Z| = sum_p sum_(w|p) [K_w:Q_p] log max(1, |zeta_1|_w, |zeta_2|_w)`.

**Consequence (Corollary 6 of the artifact).** Suppose also that `M(z)` has
kernel dimension `kappa_0 >= 1` at a point `z` off the closed set `Y` of
algebraic jumps. Then every integral form `F`, a product of linear forms at
affine points, satisfies

```text
kappa_0 a(F) + (N - kappa_0) b(F) + C deg F >= 0,
```

with `b(F) = log M(F)` and `a(F) = log M(v -> F((1,z) x v))`.

No Atiyah hypothesis enters. For `G = 1` the inequality is the product formula
plus the ultrametric inequality. The same proof works in any number of variables.
