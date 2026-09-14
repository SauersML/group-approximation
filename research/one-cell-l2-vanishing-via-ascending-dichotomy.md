---
rg: 2
id: one-cell-l2-vanishing-via-ascending-dichotomy
kind: route
title: Split one-cell complement groups on whether they are ascending HNN extensions of finitely generated groups
target: one-cell-complement-groups-have-vanishing-first-l2-betti
requires:
  - ascending-hnn-one-cell-complements-have-vanishing-l2-b1
  - non-ascending-one-cell-complements-have-vanishing-l2-b1
artifacts:
  - research/artifacts/hl-one-cell-l2-2026-09-14.md
---

Let `L` be a finite connected contractible 2-complex, `e` an open 2-cell, `K = L − e` and
`G = π₁(K)`. Exactly one of the following holds.

- `G ≅ H *_σ` for some finitely generated `H` and injective endomorphism `σ`. Then
  `b₁^(2)(G) = 0` by `ascending-hnn-one-cell-complements-have-vanishing-l2-b1`.
- No such isomorphism exists. Then `b₁^(2)(G) = 0` by
  `non-ascending-one-cell-complements-have-vanishing-l2-b1`.

So `b₁^(2)(G) = 0` in every case.

The first branch is proved and the second is open; the second is the whole remaining content of
the target.
