---
rg: 2
id: kazhdan-unitary-corners-require-finite-dimensional-mass
kind: claim
title: Almost unitary Kazhdan corners require nearly full finite-dimensional representation mass
artifacts:
  - research/artifacts/quadratic-curvature-flexible-dilation-2026-09-05.md
distinct_from:
  near-representation-amenability-dichotomy: that refuted positive charge for an individual finite-dimensional subspace under an arbitrary finitely additive charge; this uses ordinary trace on a specified finite-rank corner and measures its overlap with the closed span of all finite-dimensional subrepresentations of a genuine dilation.
  kazhdan-weak-ucp-stability-is-flexible-stability: that constructs nearby finite-dimensional corrections from supplied ucp dilations; this gives an explicit mass requirement and excludes regular-tail or reduced-algebra dilation candidates before such a correction is attempted.
---

Let `G` have a finite symmetric Kazhdan set `S` and constant `kappa>0`
in the convention

```text
dist(x,H^G)<=kappa^(-1) max_(s in S)||pi(s)x-x||.
```

Let `Pi:G->U(K)` be genuine, with `K` finite or infinite dimensional,
and let `W:C^d->K` be an isometry. For arbitrary unitaries `U_s in U(d)`
put

```text
epsilon=max_(s in S)||W^*Pi(s)W-U_s||_(2,d).
```

Let `Q_fd` be the projection onto the closed span of all finite-dimensional
invariant subspaces of Pi. Then

```text
(1/d)Tr(W^*(I-Q_fd)W)<=4epsilon/kappa^2.                 (KFM1)
```

The normalization is by the original corner dimension d, independently
of the ambient dimension. The sector `Q_fd K` can itself be infinite
dimensional; the statement does not assert positive mass for an
arbitrarily chosen individual finite-dimensional summand.

If Pi is a direct sum of a finite-dimensional exact seed of dimension k
and a representation with no finite-dimensional subrepresentations, then

```text
epsilon >= (kappa^2/4)(1-k/d).                          (KFM2)
```

For infinite G, every regular multiple and every representation induced
from a finite stabilizer belongs to the latter class. The class is closed
under Hilbert direct sums, closed invariant subspaces, and unitary
quotients. Thus an `o(d)`-dimensional exact seed plus arbitrarily many
such tails cannot produce generator corners approaching unitaries, even
with an infinite-dimensional ambient dilation.

There is also a reduced-algebra consequence. For infinite G as above,
every ucp map `Phi:C*_r(G)->M_d` and every unitary tuple `(U_s)` satisfy

```text
max_(s in S)||Phi(lambda_G(s))-U_s||_(2,d)>=kappa^2/4.    (KFM3)
```

This excludes reduced-group-algebra Stinespring constructions. It does
not exclude ucp maps from the full group algebra or dilations using
substantial genuine finite-dimensional representation content.
In particular, this is an obstruction to one family of proposed repairs
of quadratic-rank curvature, not a proof of flexible stability or
nonhyperlinearity.

DERIVATION
kazhdan-finite-sector-corner-mass-proof
