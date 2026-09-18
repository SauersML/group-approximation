---
rg: 2
id: gottschalk-via-no-topological-absorption
kind: route
title: A strict automaton would give a topological Bernoulli absorption, and no group carries one
target: gottschalk-surjunctivity-conjecture
requires:
  - no-group-carries-a-topological-bernoulli-absorption
  - strict-automata-yield-topological-bernoulli-absorptions
---

**Why sufficient.** Suppose `G` carries an injective, non-surjective automaton. By
`strict-automata-yield-topological-bernoulli-absorptions`, `A^G = A^G x Y` for some `A` and some subshift
`|Y| >= 2`. That contradicts `no-group-carries-a-topological-bernoulli-absorption`.

**Why the decomposition has content.** The goal is equivalent to the conjunction of the two premises: the goal
implies the no-absorption premise by (a) of `monomial-quantum-automata-are-topological-bernoulli-absorptions`, and
implies the hub premise vacuously. The value is that each premise is shared with another route.
- **No-absorption premise.** A common consequence of `gottschalk-surjunctivity-conjecture`,
  `quantum-surjunctivity-conjecture` and `every-group-is-dual-surjunctive`, and it implies Kaplansky stable
  finiteness over every `F_p`. It can fail only together with the goal. It is weaker than each of those three
  conjectures, so it is the natural first target on a given nonsofic group.
- **Hub premise.** It can fail while the no-absorption premise holds: a non-surjunctive group with no
  absorption at any alphabet. It implies both open transfer holes, `strict-automata-yield-strict-quantum-endomorphisms`
  (`quantum-transfer-via-topological-absorption`) and `strict-pairs-admit-post-surjective-decoders`
  (`post-surjective-decoders-via-topological-absorption`). So one proof of the hub closes the transfer hole of both
  `gottschalk-via-quantum-surjunctivity` and `gottschalk-via-dual-surjunctivity-and-decoder-transfer`, leaving
  each route with only its conjecture premise.
- **Falsifiable first step.** The hub forces a decoder that preserves the uniform measure and is post-surjective
  (`absorptions-give-post-surjective-strict-pairs`). Exhibiting a non-surjunctive group where no strict pair has
  such a decoder kills the hub and, with it, this route.
