---
rg: 2
id: c2-root-commuting-cycle-splitting-proof
kind: route
title: Lift all commuting root generators simultaneously to the Steinberg cover
target: c2-root-commuting-cycle-is-maslov-trivial
requires: []
artifacts:
  - research/artifacts/c2-root-commuting-graph-maslov-audit-2026-08-21.md
---

For each root `gamma`, lift `X_gamma(1)` to the universal cover of `Sp4(R)`
using the real-root path `t -> X_gamma(t)`.  If `gamma` and `delta` commute,
their root subgroups define a homomorphism `R^2 -> Sp4(R)`.  Since `R^2` is
simply connected, it has a unique lift to the universal cover, again a
homomorphism.  Thus the canonical root lifts commute on every graph edge.
The universal property of the graph product gives a homomorphism

```text
A(G_com) -> universal cover of Sp4(R)
```

lifting the canonical map to `Sp4(Z)`.  Projecting to the connected
three-fold cover proves that the pulled-back Deligne extension splits, so its
cohomology class and every cycle holonomy vanish.  Kassel Proposition 2.1
gives an algebraic check of the simultaneous edge lifting: relations
(2.1)--(2.3) say that his eight Steinberg root lifts commute on precisely all
twelve graph edges.

For completeness, (2.1)--(2.3) give twelve edges and four maximal cliques

```text
{beta, alpha+beta, 2alpha+beta},
{alpha, 2alpha+beta, -beta},
{-beta, -(alpha+beta), -(2alpha+beta)},
{-alpha, beta, -(2alpha+beta)}.
```

Their only induced cycle is the four-long-root cycle displayed in the target
claim.  Kassel Section 2.4 instead locates the central generator at the
noncommuting rank-one word `w_gamma^4`, with
`w_gamma=x_gamma x_(-gamma)^(-1) x_gamma` for a long root.
