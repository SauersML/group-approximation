---
rg: 2
id: some-braid-group-has-no-proper-cat0-action
kind: claim
title: Some braid group admits no proper isometric action on a proper CAT(0) space
distinct_from:
  every-braid-group-acts-properly-on-a-proper-cat0-space: that claim is the positive answer to the non-cocompact reading of Problem 3.6; this one is its negation
---

There is `n` such that `B_n` admits no proper isometric action on any proper
(complete, locally compact) CAT(0) metric space. By route
`braid-not-cat0-from-no-proper-cat0-action` this gives the negative answer to
Zaremsky Problem 3.6.

Any such `n` is at least 8, since `B_n` is CAT(0) for `n <= 7`.

## Attempts

- Semisimplicity arguments need cocompactness or cellular actions with finitely
  many shapes, so they do not reach this claim. An obstruction here would have
  to rule out actions with parabolic isometries; no candidate is known.
- Forcing zero translation length through Bridson's centralizer criterion
  (arXiv:0908.0685, the Kapovich–Leeb/Bridson template for `Mod(Σ_g)`, `g ≥ 3`)
  cannot work here. By `braid-centralizer-characters-detect-infinite-order`,
  every infinite-order element of `B_n` or `Mod(S_{0,n+1})` has infinite order
  in the abelianization of its centralizer. Notes:
  `notes/some-braid-group-has-no-proper-cat0-acti-swarm-2026-09-16.md`.
