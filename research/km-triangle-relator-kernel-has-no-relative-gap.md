---
rg: 2
id: km-triangle-relator-kernel-has-no-relative-gap
kind: claim
title: The Kac-Moody triangle relator kernel has no finite-word relative Kazhdan gap
distinct_from:
  kernel-inner-tree-face-balancing-collapses: that rules out inner-conjugation balancing by Bass-Serre centralizer rigidity; this rules out arbitrary finite-word coercive correction through failure of relative property (T), without assuming that any face map is multiplicative or inner.
  finite-relator-reservoir-repairs-every-fd-packet: that asks for packet-dependent cp corrections inside one finite word reservoir and remains open; this proves that such a reservoir can never work by a dimension-uniform Poincare inverse controlling distance to the relator-kernel-fixed space.
  position-window-ucp-sections-collapse-to-folner-vectors: that applies the trivial character to rule out orthogonal position windows; this uses the extension theorem for relative property (T) to rule out a finite relator Laplacian gap, with no position decomposition or formula for a ucp map.
  three-face-ucp-balancing-needs-macroscopic-tree-motion: that gives an operator-norm displacement floor for every triangular ucp balance; this explains why the native relators cannot supply that displacement through a uniform spectral inverse.
---

**ESTABLISHED (spectral-correction no-go).**  In the Kac--Moody triangle
setting, write

```text
1 -> K -> G_0=P_12 *_(P_2) P_23 -> Lambda -> 1,          (NRG1)
```

where `Lambda` is one of the infinite simple Kazhdan groups from
`simple-kazhdan-kac-moody-lattices-exist`.  Then the pair `(G_0,K)` does
**not** have relative property `(T)`.

For a normal subgroup, the standard extension theorem says

```text
G has property (T)
  iff (G,K) has relative property (T) and G/K has property (T). (NRG2)
```

Here `G_0/K=Lambda` has property `(T)`, whereas the infinite virtually free
group `G_0` does not: it acts properly on its Bass--Serre tree (equivalently,
it has the Haagerup property), and an infinite group cannot have both the
Haagerup property and property `(T)`.  Equation `(NRG2)` proves the assertion.

Equivalently, for every finite `F subset G_0` and every `delta>0`, there are a
unitary representation `pi` and a unit vector `xi` such that

```text
max_(g in F) ||pi(g)xi-xi|| < delta,       H_pi^K={0}.   (NRG3)
```

This gives an exact finite-reservoir consequence.  Fix any finite word set
`W` and a free basis `n_1,...,n_r` of the native face kernel whose normal
closure is `K`.  Let

```text
B_W={a(n_j^(+-1)-1)b : a,b in W, 1<=j<=r}.              (NRG4)
```

There is no constant `C_W` such that, in every unitary representation,

```text
dist(xi,H_pi^K)^2
 <= C_W sum_(x in B_W) ||pi(x)xi||^2.                    (NRG5)
```

Indeed, apply `(NRG3)` with `F` containing every group word occurring on the
two sides of the differences in `(NRG4)`.  The right side of `(NRG5)` tends
to zero, while `H_pi^K={0}` makes the left side equal to one.  The same
argument rules out every positive finite sum of squares made from a fixed
finite relator reservoir as a uniformly invertible operator on the complement
of the `K`-fixed vectors.

**Exact scope.**  This is a no-go beyond multiplicative or inner face maps:
it rules out the natural construction that solves simultaneous positivity by
applying a dimension-uniform inverse of a finite relator Laplacian.  It does
not refute `finite-relator-reservoir-repairs-every-fd-packet`.  That claim
allows the correction coefficients to depend singularly on the finite packet
and asks only for cp repair, not a coercive estimate on every unitary
representation; moreover the representations in `(NRG3)` need not be
finite-dimensional.  Thus the surviving positive route must use precisely
noncoercive, packet-dependent complete-positive geometry rather than a
relative-Kazhdan projection.

**Finite-dimensional upgrade.**  The final caveat is removed for this
virtually free ambient group by
`km-triangle-relative-gap-failure-has-fd-full-support-witnesses`: RFD
coefficient approximation followed by deletion of the trivial quotient
summand produces genuine finite-dimensional witnesses with `H_rho^K=0`,
ideal support `z_rho=1`, and arbitrarily small energy for every fixed
reservoir.  This strengthens the spectral no-go but still does not refute the
packet-dependent Choi repair claim.

DERIVATION
property-t-extension-dichotomy-kills-relator-gap
