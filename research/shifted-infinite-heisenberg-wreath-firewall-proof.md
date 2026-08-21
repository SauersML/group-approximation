---
rg: 2
id: shifted-infinite-heisenberg-wreath-firewall-proof
kind: route
title: Use unbounded commuting Weyl rank, then shift the carrier over a Kazhdan orbit
target: shifted-infinite-heisenberg-wreath-exact-mci-is-hyperlinear
requires:
  - sofic-implies-hyperlinear
---

On a finite-dimensional `lambda`-eigenspace of the central element `z`, let
`q` be the order of `lambda`. The first `N` commuting Weyl pairs act on the
joint spectrum with free `(Z/q)^N` orbits, so `q^N` divides the eigenspace
dimension for every `N`. Therefore `q=1` and every finite-dimensional
representation kills `z`.

The index shift makes the tower finitely generated and amenable. Its
restricted wreath product with an infinite sofic property-`(T)` group is
finitely generated, recursively presented and sofic. The subgroup translates
the distinguished central element through distinct lamp sites, so every
nonzero power has an infinite orbit. Exact finite-dimensional carrier energy
vanishes by the first paragraph, while the canonical regular energy is
positive by orthogonality of the distinct lamp words. Soficity gives
hyperlinearity and proves that no uniform approximate collapse follows.
