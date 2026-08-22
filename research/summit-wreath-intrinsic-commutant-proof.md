---
rg: 2
id: summit-wreath-intrinsic-commutant-proof
kind: route
title: Kill nonidentity Fourier coefficients by infinite lattice-conjugacy orbits
target: summit-wreath-intrinsic-lattice-commutant-is-abelian
requires:
  - coset-bernoulli-action-is-essentially-free
---

Write `A=L^infinity(X)`.  First observe that every `g!=1` in `Gamma` has an
infinite conjugacy orbit under `Lambda`.  Otherwise

```text
[Lambda:C_Lambda(g)]<infinity,                          (1)
```

so `g` centralizes a finite-index subgroup of `SL_3(Z)`.  That subgroup is
Zariski dense in `SL_3`, hence `g` is central in `SL_3(Q)`.  The only
rational scalar of determinant one in dimension three is `1`, a
contradiction.

Take `z in L(Lambda)' cap N` and use its crossed-product Fourier expansion

```text
z=sum_(g in Gamma) a_g u_g,       a_g in L^2(A).         (2)
```

For every `lambda in Lambda`, the equality `u_lambda z u_lambda^*=z`
identifies the coefficient at `lambda g lambda^-1` with a translate of
`a_g`.  In particular its `L^2` norm equals `||a_g||_2`.  If `g!=1`, the
orbit from `(1)` is infinite; square summability of `(2)` therefore forces
`a_g=0`.  Hence `z=a_1`, and commutation with `Lambda` says exactly
`a_1 in A^Lambda`.  The reverse inclusion is immediate, proving `(SIC2)`.

For `(SIC3)`, every finite-dimensional abelian star algebra is unitarily
conjugate to

```text
{diag(z_1 I_(m_1),...,z_r I_(m_r)):z_j in C},       r<=d.
```

Its unitary group is a weighted `r`-torus.  Choose an `epsilon/2`-net of
the circle in ordinary distance with at most `C/epsilon` points and take
the product grid.  Coordinatewise error at most `epsilon/2` gives normalized
Hilbert--Schmidt error at most `epsilon/2`, irrespective of the block
multiplicities.  The grid has at most `(C/epsilon)^r<=(C/epsilon)^d`
points, proving `(SIC3)`--`(SIC4)`.
