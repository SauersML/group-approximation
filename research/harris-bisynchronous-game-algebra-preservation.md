---
rg: 2
id: harris-bisynchronous-game-algebra-preservation
kind: claim
title: Every synchronous game has an equal-size bisynchronous game with the same game algebra
distinct_from:
  oracularizable-tracial-nonru-game-exists: that preserves a particular tracial non-RU source while adding compatible incidence measurements; this is a general exact game-algebra conversion to equal question and answer cardinalities.
  fu-mastel-zhang-cc-to-synchronous-cv: that is a soundness-preserving constraint-variable conversion with an oracular completeness interface; this is a *-isomorphism of universal game algebras and targets bisynchrony.
---

For every finite synchronous game `G` with `n` questions and `k` answers,
there is an explicitly constructed bisynchronous game `G_tilde` with `nk`
questions and `nk` answers such that

```text
A(G_tilde) is *-isomorphic to A(G).
```

Consequently perfect commuting representations and nonzero
`R^omega`-representations are preserved.  In particular, a synchronous game
with a perfect `qc` strategy but no perfect `qa` strategy yields an
equal-input/output bisynchronous game with the same separation.  Its perfect
correlations are expressed by a square magic unitary.
