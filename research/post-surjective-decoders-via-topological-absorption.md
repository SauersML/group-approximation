---
rg: 2
id: post-surjective-decoders-via-topological-absorption
kind: route
title: Turn a strict automaton into a topological Bernoulli absorption and take its first coordinate as the decoder
target: strict-pairs-admit-post-surjective-decoders
requires:
  - strict-automata-yield-topological-bernoulli-absorptions
  - absorptions-give-post-surjective-strict-pairs
---

Let `G` carry an injective, non-surjective automaton.
1. By `strict-automata-yield-topological-bernoulli-absorptions`, some `A^G` absorbs a subshift `Y` with `|Y| >= 2`.
2. By (ii) of `absorptions-give-post-surjective-strict-pairs`, the pair `(Psi^-1(., y_0), pr_1 Psi)` is a strict
   pair over `A` whose decoder is post-surjective.

This is the target, over the alphabet `A`.
