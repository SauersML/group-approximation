---
rg: 2
id: absorptions-via-locally-balanced-decoders
kind: route
title: Find a locally balanced decoder, then glue its one-site lifts into an absorption
target: strict-automata-yield-topological-bernoulli-absorptions
requires:
  - strict-pairs-admit-locally-balanced-decoders
  - locally-balanced-decoders-admit-translation-lifts
---

Let `G` carry an injective, non-surjective automaton.
1. By `strict-pairs-admit-locally-balanced-decoders`, some strict pair `(tau, sigma)` over a finite alphabet `A` has
   a locally balanced decoder `sigma`.
2. `sigma` is not injective. Since `sigma o tau = id`, if `sigma` were injective it would be bijective, and then
   `tau = sigma^-1` would be onto.
3. By `locally-balanced-decoders-admit-translation-lifts`, `G` carries a topological Bernoulli absorption at some
   alphabet size.

This is the target.

**Why the split is useful.** The two premises can fail independently.
- The first is a pure counting condition on one automaton. It already implies
  `strict-pairs-admit-post-surjective-decoders`, by `post-surjective-decoders-via-local-balance`.
- The second is a gluing condition. By (E) of `extension-decoders-are-locally-balanced`, it amounts to the
  commutation of one-site lifts with finitely many of their translates.
- Conversely, the target implies the first premise, by (A) of the lemma.
