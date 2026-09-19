---
rg: 2
id: kazhdan-projection-not-in-l1-proof
kind: route
title: The regular representation is injective on the convolution algebra
target: kazhdan-projection-not-in-l1
requires: []
artifacts:
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
---

## Direct proof

The left regular representation is injective on `l^1(Gamma)`: for
`a in l^1(Gamma)`, `lambda(a) delta_e = a` as an element of `l^2(Gamma)`, so
`lambda(a) = 0` forces `a = 0`.  It factors through `C*_max(Gamma)`.

The Kazhdan projection satisfies `pi(p) = ` the orthogonal projection onto the
`pi`-invariant vectors, in every unitary representation `pi`.  For the regular
representation of an infinite group there are no invariant vectors — an
invariant `l^2` function is constant, hence zero — so `lambda(p) = 0`.  For
the trivial representation `epsilon(p) = 1`, so `p != 0`.

If `p` were the image of some `a in l^1(Gamma)`, then `lambda(a) = 0`, hence
`a = 0`, hence `p = 0`, contradicting `epsilon(p) = 1`.

For the averages: `|| . ||_{C*_max} <= || . ||_{l^1}`, so an `l^1`-Cauchy
sequence has an `l^1` limit whose image is the `C*_max` limit.  Since
`mu^{*n} -> p` in `C*_max` by the spectral gap, `l^1`-Cauchyness would put `p`
in the image of `l^1`, which the previous paragraph forbids.

Finally, an isometric action `alpha` of `Gamma` on a Banach space `A` gives
`|| alpha(a) ||_{B(A)} <= || a ||_{l^1}` and nothing sharper without a
Hilbertian structure; so `alpha(mu^{*n})` need not converge and `alpha(p)` is
undefined.  On a Hilbert space the `C*_max` bound is available and both exist,
which is exactly the passage the transport argument makes.
