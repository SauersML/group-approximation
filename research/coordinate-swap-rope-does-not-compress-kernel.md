---
rg: 2
id: coordinate-swap-rope-does-not-compress-kernel
kind: claim
title: Opposite quotient coordinates make the rope HNN symmetric but stop kernel compression
distinct_from:
  mf-safe-asymmetric-hnn-replacement: that is the live request for a graph-HNN replacement satisfying both finite-presentation semantics and MF permanence; this rules out the natural coordinate-swap symmetrization.
  sl3-hnn-sits-in-shulman-symmetric-double: that embeds a centralizer HNN into an untwisted double without having to impose a recursively presented quotient kernel.
---

ESTABLISHED NO-GO.  Let `Q=F/N`, `S=F *_N F`, and define two maps to
`Q times Q` by putting the quotient map in opposite coordinates on the two
free factors:

```text
tau_0|F_0=(q,1),       tau_0|F_1=(1,q),
tau_1|F_0=(1,q),       tau_1|F_1=(q,1).                (CSR1)
```

The graph embeddings `theta_i(s)=(s,tau_i(s))` are exchanged by the
coordinate-swap automorphism of the base.  Consequently a faithful matrix
corona embedding can be doubled with its swap and an exact block-swap unitary;
this removes the operator-norm compatibility problem.

It also removes the rope compression.  Before quotienting the two free
coordinates by `N`, take `n in N` and write `g` for the common image of its two
factor copies in the benign double.  The two finite families of HNN relations
give only

```text
u(g,n,1)u^-1=(g,1,n),
u(g,1,n)u^-1=(g,n,1).                                 (CSR2)
```

Relations `(CSR2)` say that conjugation by `u` swaps the two unreduced kernel
coordinates.  They do not imply `n=1`; for example they hold in the
semidirect product where an order-two letter swaps the two copies of `F`.
Thus the candidate finite presentation does not impose the recursive relators
and does not present the intended rope group.

This failure is structural for any symmetry which already lifts to the
pre-quotient coordinates: an ambient automorphism preserves the missing
relations rather than generating them.  A viable repair must obtain analytic
compatibility without a symmetry that lifts before `N` is killed.
