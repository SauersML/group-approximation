---
rg: 2
id: every-artin-twisted-brin-thompson-group-embeds-in-fp-group
kind: claim
title: For every Artin group A the twisted Brin-Thompson group AV_A embeds in a finitely presented group
distinct_from:
  artin-groups-satisfy-boone-higman: that asks for finitely presented SIMPLE envelopes of the Artin groups themselves, over those with solvable word problem; this asks for a finitely presented host, not necessarily simple, of the larger group AV_A, for every Artin group.
  every-artin-group-has-solvable-word-problem: that is the word problem for all Artin groups; this is the embedding statement, equivalent to it through self-twisted-bt-group-fp-embedding-iff-solvable-wp, and kept as its own claim because Zaremsky poses the embedding.
---

**OPEN.** For every Artin group `A` on a finite nonempty generating set, the twisted
Brin–Thompson group `AV_A`, for `A` acting on itself by left translation, embeds in a
finitely presented group.

By `self-twisted-bt-group-fp-embedding-iff-solvable-wp` this is equivalent to
`every-artin-group-has-solvable-word-problem`. The routes
`artin-twisted-bt-fp-hosts-from-solvable-word-problem` and
`artin-solvable-word-problem-from-twisted-bt-fp-hosts` record the two directions.

## Attempts

- **Through the word problem** (route
  `artin-twisted-bt-fp-hosts-from-solvable-word-problem`). This is equivalent, not
  easier. The known classes give the yes answer for their members only (artifact §5).
- **Through `AV_A` being finitely presented itself.** Dead. The implication is valid,
  but its premise fails for every infinite group by Zaremsky's criterion (artifact §4,
  landing as `self-twisted-bt-group-of-infinite-group-is-not-fp`).
- **Explicit hosts** (artifact §6, Lemma 3, unreviewed).
  - If `A ≤ Δ`, `Δ` acts faithfully on `T` with type (A) and some `A`-orbit is free,
    then `AV_A` embeds in the finitely presented simple group `TV_Δ`.
  - Any such `Δ` already forces a solvable word problem for `A`, so this is a strategy
    for the word problem, not a weaker target.
  - Unexplored: whether the type (A) actors of Belk–Fournier-Facio–Hyde–Zaremsky
    (arXiv:2503.21882) for braid groups have free orbits.
