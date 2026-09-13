---
rg: 2
id: proper-and-free-type-fhn-coincide
kind: claim
title: "A group acts properly and cocompactly on an (n-1)-acyclic complex iff it acts freely and cocompactly on one"
artifacts:
  - research/artifacts/zp-fpn-fhn-2026-09-13-part1.md
---

Let `n ≥ 0`. Suppose a group `G` acts cellularly on an `(n−1)`-acyclic CW
complex `X` with finite cell stabilizers and finitely many orbits of cells.
Then `G` acts freely and cellularly on some `(n−1)`-acyclic CW complex `W`
with finitely many orbits of cells. The converse is trivial.

So the printed reading of `FH_n` in Zaremsky Problem 1.4 (proper actions)
and the Bestvina–Brady and Leary reading (free actions) define the same
class of groups.

Construction (Theorem C of the artifact): `W ⊆ X × J`, where `J` is the
`(n+1)`-fold join of the discrete set `G`. Over a cell `e` of `X`, `W` takes
the finite `(n−1)`-connected subcomplex `J(S_e)`, where `S_e` is the finite
set of `g` with `K(e) ⊆ gC` for a fixed finite subcomplex `C` meeting every
orbit. Comparing the skeletal spectral sequences gives `H_j(W) ≅ H_j(X)` for
`j ≤ n−1`.
