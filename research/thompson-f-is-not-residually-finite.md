---
rg: 2
id: thompson-f-is-not-residually-finite
kind: claim
title: Thompson's group F is not residually finite, so no residually finite group contains a copy of F
distinct_from:
  self-similar-hosts-contain-only-residually-finite-groups: that shows subgroups of self-similar groups are residually finite and deduces that the simple group V embeds in no self-similar group; this shows that F, which is not simple, still fails residual finiteness, through a displacement commutator argument
---

**Statement.** There is a nontrivial element of Thompson's group `F` that lies in
every finite-index normal subgroup of `F`. So `F` is not residually finite, and
since subgroups of residually finite groups are residually finite, no residually
finite group has a subgroup isomorphic to `F`.

The proof is the route `thompson-f-is-not-residually-finite-proof`. It uses only
the piecewise-linear model of `F` on `[0,1]` (dyadic breakpoints, slopes powers of
2). The fact itself is classical: it follows from Cannon–Floyd–Parry's results
that `[F,F]` is simple and every proper quotient of `F` is abelian (Enseign. Math.
42 (1996), §4). The route gives a self-contained argument that needs neither.

**Use.** A residually finite torsion-free group of type F_∞ with infinite
cohomological dimension answers Zaremsky Problem 2.8; see
`tf-finf-infinite-cd-omits-f-via-residual-finiteness`.
