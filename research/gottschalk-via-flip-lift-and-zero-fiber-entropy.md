---
rg: 2
id: gottschalk-via-flip-lift-and-zero-fiber-entropy
kind: route
title: Strictness gives a positive-entropy lift, which a zero-entropy law would forbid
target: gottschalk-surjunctivity-conjecture
requires:
  - strict-split-pairs-carry-positive-entropy-flip-lifts
  - ca-bernoulli-lifts-have-zero-fiber-entropy
artifacts:
  - research/artifacts/decoder-fiber-flip-lifts-2026-09-12.md
---

**Dead.** Every injective automaton has a cellular decoder. If it were strict,
the flip lift would give an invariant lift of uniform Bernoulli with positive
fiber entropy. A universal zero-entropy law for such lifts would forbid this and
prove surjunctivity.

The law is false: the XOR automaton over `Z` violates it over a surjunctive group
(`xor-lift-of-bernoulli-has-positive-fiber-entropy`, which invalidates this
route). Its second prerequisite is refuted and never becomes established, so
the route is dead on two counts.

A live version needs an averaged fiber-entropy bound that uses the section `tau`
and survives nonamenable boundaries. Section 5 of the artifact explains why such
a bound is equivalent to the goal, and that it would also prove stable finiteness
of `F_p[G]` for every group.
