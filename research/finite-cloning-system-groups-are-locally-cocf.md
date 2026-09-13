---
rg: 2
id: finite-cloning-system-groups-are-locally-cocf
kind: claim
title: "Every cloning system on finite groups has a locally co-context-free Thompson-like group"
artifacts:
  - research/artifacts/zp-lehnert-2-16-2026-09-13.md
---

For every cloning system `((G_n), (ι), (ρ_n), (κ))` (Witzel–Zaremsky) in which
every `G_n` is finite, the Thompson-like group `T(G_*)` is locally
co-context-free: every finitely generated subgroup of `T(G_*)` is coCF. (When
`T(G_*)` is finitely generated this is exactly "coCF", since coCF passes to f.g.
subgroups.) This is the affirmative answer to the coCF sub-question of Zaremsky
Problem 2.16 (`zaremsky-2-16-lehnert-conjecture`).

## Attempts

- Positive for the twisted direct-power / labeled-`V` family
  (`twisted-direct-power-cloning-finite-groups-are-cocf`, Berns-Zieve et al.
  Thm 4.3) and for FSS / local-similarity groups under a mild hypothesis
  (Farley, arXiv:1406.4590). The pushdown-automaton method reads the tree
  address off the stack and multiplies finite `G_n`-labels; the obstruction in
  Berns-Zieve Remark 4.4 was only the states *acting* on the tree (Grigorchuk
  labels), which finite static labels avoid.
- Obstruction to a general "yes": period growth of a coCF group is `⪯ exp(n^4)`
  (Bishop–Bodart–Issini–Perego, arXiv:2601.13058, Thm 2.7). A finite-group
  cloning system whose `T(G_*)` realises element orders `≻ exp(n^4)` in words of
  length `n` would refute this claim; that negation is
  `some-finite-cloning-system-group-is-not-locally-cocf`. Whether any compatible
  cloning family on finite groups exceeds `V`'s `exp(n^2)` order growth is the
  crux; bounded-exponent families (`G_n = A^n`, signed permutations `S_n^±`)
  cannot. Not resolved by this lane.
