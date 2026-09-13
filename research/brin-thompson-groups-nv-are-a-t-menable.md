---
rg: 2
id: brin-thompson-groups-nv-are-a-t-menable
kind: claim
title: "Every Brin-Thompson group nV (n >= 2) has the Haagerup property"
---

For every `n >= 2`, the Brin–Thompson group `nV` admits a proper conditionally
negative definite function, equivalently a metrically proper affine isometric
action on a Hilbert space. Since `nV <= mV` for `n <= m`, the claim for all `n`
is equivalent to the claim for arbitrarily large `n`.

This is the "yes" answer to the Haagerup part of Zaremsky Problem 2.7
(`zaremsky-2-07-brin-thompson-nv-haagerup-or-t`).

## Attempts

- **Farley-type charts (dies for n >= 2).** For `V`, let `X` be the set of
  pairs `(U, φ)` with `U ⊆ C` clopen and `φ: C → U` a homeomorphism in the
  Thompson groupoid, `V` acting by `g·(U, φ) = (gU, g∘φ)`, and `A ⊆ X` the
  standard cylinder charts `ι_w(u) = wu`. Then `g∘ι_w` is standard exactly
  when `[w]` lies inside a leaf of the reduced domain tree of `g`, so
  `|gA Δ A|` is the number of internal nodes of the reduced domain and range
  trees: finite, and proper in `g`. This gives a-T-menability of `V`.
  The same construction for `nV` with standard brick charts is not
  commensurated: `g(x, y) = (x, y)` on `[0] x C` and `(x, s(y))` on `[1] x C`,
  with `s` swapping the first letter, is not canonical on any brick
  `C x [v]`, and there are infinitely many such bricks. Breaks in dimension
  `>= 2` are codimension-one, so every brick-like family is broken infinitely
  often.
- **Stein–Farley complex (dies).** The cube complex of expansions of `nV`
  (Fluch–Marschler–Witzel–Zaremsky) is not CAT(0) for `n >= 2`: splitting a
  piece in direction 1 and then both halves in direction 2 gives the same
  vertex as the other order, a 6-cycle in the 1-skeleton that no cube corner
  or pair of squares fills. So its 1-skeleton is not a median graph.
- **Next.** A wall structure whose walls are codimension-one objects counted
  finitely: maximal break segments of `g` along brick faces, with charts that
  record the transverse extent. Any proper cubical action must be
  infinite-dimensional, by `FW_infinity` (Fournier-Facio–Wu–Zaremsky,
  arXiv:2603.24687).
