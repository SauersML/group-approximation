---
rg: 2
id: transport-identity-gives-reciprocal-memory-entropy-bound
kind: claim
title: The single-site output entropy of an injective automaton is at least log |A| over its left-inverse memory size
distinct_from:
  injective-ca-images-have-full-single-site-entropy: that asks for the full bound log |A|, which is equivalent to the goal; this is the weaker unconditional bound (log |A|)/|N| that the random-order transport identity yields by itself, tight term by term.
  decoder-window-fiber-bound-loses-exactly-the-boundary: that is a per-window counting bound losing the right boundary on nonamenable groups; this is a single-site bound from the exact transport identity, valid over every group with no counting.
artifacts:
  - research/artifacts/three-point-decoder-transport-obstruction-2026-09-12.md
  - research/artifacts/random-order-decoder-transport-2026-09-12.md
---

**ESTABLISHED** by `transport-identity-gives-reciprocal-memory-entropy-bound-proof`.

Let `G` be any group, `A`, `B` finite alphabets, and `kappa : A^G -> B^G` an injective automaton with a left inverse
of memory `N` containing `e`. Under the uniform product measure on `A^G`,

    H( kappa(x)(e) )  >=  (1 / |N|) log |A| .

This is exactly what the random-order transport identity (`injective-ca-random-order-transport-identity`) gives on its
own: the identity splits `log |A|` into `|N|` averaged conditional mutual informations into `y(e)`, each at most
`H(y(e))`. The per-term bound is tight (one term can reach `H(y(e))`), so no term-by-term argument beats the constant
`1/|N|`. Domination (`injective-ca-random-order-transport-is-dominated`) is the constant-`1` case, equal to the goal.

## Attempts
- **Exact at `|N| = 1`** (`kappa(x)(e)` determines `x(e)`), with a gap for every `|N| >= 2`; the bound degrades to `0`
  as `|N| -> infinity`. So a proof of the full bound must beat the reciprocal, i.e. use realizability of `y` as a
  finite block code of i.i.d. `x`, not only the information relations among the decoder sites. See
  `three-point-decoder-memory-injective-ca-are-surjective`.
