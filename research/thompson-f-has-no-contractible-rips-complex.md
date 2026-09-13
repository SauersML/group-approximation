---
rg: 2
id: thompson-f-has-no-contractible-rips-complex
kind: claim
title: No Rips complex of Thompson's group F is contractible
distinct_from:
  thompson-f-is-not-automatic: that is the open claim that F has no automatic structure; this is the established fact that no Cayley graph of F has a contractible clique complex, which rules out automaticity only in combination with a theorem about automatic groups
  rips-complexes-of-integer-lattices-are-contractible: that is Virk's positive theorem for Z^n; this is a negative statement for F, which contains Z^n for every n
---

**ESTABLISHED** (route `thompson-f-has-no-contractible-rips-complex-proof`).

For every finite generating set `S` of Richard Thompson's group `F` and every
`r >= 0`, the Rips complex `P_r(F,S)` is not contractible.

The reason is dimension: `F` is torsion-free and contains `Z^n` for every `n`,
so it has infinite cohomological dimension and no finite `K(F,1)`. This is the
input behind the parenthetical of Zaremsky Problem 4.1
(`zaremsky-4-01-amenable-automatic-contractible-rips`).
