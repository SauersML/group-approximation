---
rg: 2
id: stw87-diagonal-order-zero-maps-annihilate-matrix-colours-proof
kind: route
title: Test a diagonal order-zero map against point evaluations
target: stw87-diagonal-order-zero-maps-annihilate-matrix-colours
requires: []
---

It is enough to prove that every order-zero positive functional on `M_n`,
`n>=2`, is zero.  Suppose that such a functional `omega` is nonzero.  Write

```text
omega(a)=Tr(ha)
```

for a nonzero positive matrix `h`.  Choose a unit eigenvector `xi` of `h`
with eigenvalue `lambda>0`, and choose a unit vector `eta` orthogonal to
`xi`.  The unit vectors

```text
v_+=(xi+eta)/sqrt(2),    v_-=(xi-eta)/sqrt(2)
```

are orthogonal.  If `p_+` and `p_-` are their rank-one projections, then
`p_+p_-=0`, whereas

```text
omega(p_+)=omega(p_-)
  =(lambda + <h eta,eta>)/2 > 0.
```

This contradicts order zero, since the positive scalar images of two
orthogonal positive elements must have product zero.  Hence `omega=0`.

Now let `theta:F->ell^infinity(X)` be c.p.c. and order zero.  Its restriction
to a summand `M_(n_j)` is order zero.  For every `x in X`, point evaluation
composed with that restriction is an order-zero positive functional, so it
is zero when `n_j>=2`.  Since the point evaluations separate
`ell^infinity(X)`, the restriction itself is zero.  This proves the first
assertion without a structure theorem for order-zero maps.

For the quantitative assertion, choose distinct points `x_1,...,x_n` in
`X`.  Their matrix units have finite propagation, so

```text
iota(e_ij)=e_(x_i x_j)
```

defines a *-homomorphism into `C*_u(X)`.  The first assertion says that the
only c.p.c. order-zero map from `M_n` to `ell^infinity(X)` is the zero map.
On the other hand, `E_X iota` is contractive and sends the unit of `M_n` to
the norm-one projection `sum_i e_(x_i x_i)`.  Therefore

```text
norm(E_X iota)=1,
```

and every map occurring in the infimum in `(M)` is zero.  The infimum is
therefore exactly one.
