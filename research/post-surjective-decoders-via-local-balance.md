---
rg: 2
id: post-surjective-decoders-via-local-balance
kind: route
title: A locally balanced decoder is a post-surjective decoder
target: strict-pairs-admit-post-surjective-decoders
requires:
  - strict-pairs-admit-locally-balanced-decoders
  - extension-decoders-are-locally-balanced
---

Let `G` carry an injective, non-surjective automaton.
1. By `strict-pairs-admit-locally-balanced-decoders`, there is a strict pair `(tau, sigma)` over some finite alphabet
   `A`, with `sigma` locally balanced for some lift set `S`.
2. By (D1) of `extension-decoders-are-locally-balanced`, `sigma` is post-surjective. In fact it is strongly
   post-surjective: a change of the output on a finite set `E` lifts to a change of the input inside `ES`.

This is the target, over the alphabet `A`.
- This route is weaker than `post-surjective-decoders-via-topological-absorption`, because its premise is implied
  by that route's premise.
- By (B) of the lemma, its premise also follows from the decoder-extension form of
  `strict-automata-yield-strict-quantum-endomorphisms`.
