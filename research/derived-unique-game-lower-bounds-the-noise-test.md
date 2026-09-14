---
rg: 2
id: derived-unique-game-lower-bounds-the-noise-test
kind: claim
title: On learnable matchings the folded long-code noise test is no more sound than the derived unique game
distinct_from:
  separated-small-pairing-families-defeat-the-noise-test: that is the existence statement for separated subexponential pairing families, with random low-value source games; this is the instance-by-instance lower bound for any 2-to-1 game with decodable matchings, in terms of the derived unique game.
  affine-long-code-test-has-no-uniform-soundness: that is one explicit affine family of source games; this bounds the test on every instance whose matchings can be decoded.
artifacts:
  - research/artifacts/unique-games-smooth-design-richness-2026-09-11.md
---

**ESTABLISHED.** Let `G` be a regular 2-to-1 game with left alphabet `[N]` and
right alphabet `[n]`. Let `UG_der(G)` be the unique game whose left vertices are
the pairs `(u,pi)`, for each distinct matching `pi` induced at `u`. Each
`(u,pi)` is labeled by a pair of `pi`, and the constraints are the bijections
`pairs(pi) -> [n]` given by `G`'s projections.

Suppose each left vertex has a shift-invariant decoder that recovers the edge
matching from one noisy pull-back table with error at most `e`. Then the folded
long-code noise test of Braverman--Khot--Minzer satisfies

```text
val(R_(rho,m)(G)) >= 1/m + (1-1/m) rho^3 val(UG_der(G))^2 - 2e,
```

and `val(UG_der(G)) >= val(G)`. If each matching occurs on one edge per left
vertex, `val(UG_der(G)) = 1`, so the test output has value near `rho^3` whatever
`val(G)` is.

Credit: the lemma was proposed by the parallel lane `ugc-2` on 2026-09-11 and is
re-derived in the artifact (Section 2). Consequence: through this test, UGC on
learnable-matching instances needs the derived unique game to be hard already,
which is circular.
