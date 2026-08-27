---
rg: 2
id: graph-endomorphism-britton-embedding-proof
kind: route
title: Preserve both associated-subgroup membership tests under the graph embedding
target: graph-endomorphism-phase-hnn-embeds-formanek-procesi
requires:
  - formanek-procesi-diagonal-hnn-is-residually-finite
---

The base map in `(GEH3)` is injective because `theta` is injective.  It sends
the first associated subgroup `L times 1` into the first associated subgroup
of `(GEH2)`, and sends the graph subgroup

```text
{(g,theta(g)):g in L}
```

to the diagonal subgroup `{(theta(g),theta(g)):g in L}`.  Hence it respects
the HNN isomorphisms and defines a homomorphism `(GEH3)`.

It also reflects membership in both associated subgroups.  For `(g,h)` in
the source base,

```text
(theta(g),h) in L times 1       iff h=1,
(theta(g),h) in diagonal(L)     iff h=theta(g).           (GEH4)
```

The right sides say exactly that `(g,h)` lies in the first subgroup or in
the graph of `theta`, respectively.  Thus a Britton-reduced word in
`E_theta` maps to a Britton-reduced word in `H^+(L)` and cannot become
trivial.  This proves injectivity.

The coefficient covariance follows by applying `(GEH1)` to
`a_i^(0)(a_j^(0))^(-1)` and using that the two direct factors commute.
Residual finiteness and hyperlinearity descend to subgroups of `(GEH2)`.
