---
rg: 2
id: injective-ca-admit-countable-transitive-decoder-fiber
kind: claim
title: Every injective full-shift automaton admits a decoder with one countable transitive fiber
distinct_from:
  gottschalk-surjunctivity-conjecture: this asks for one countable fiber of some local decoder over a transitive configuration; the split-fiber theorem makes it an equivalent unresolved criterion after the finitely generated reduction.
  fixed-gottschalk-test-group-is-surjunctive: that concentrates the conjecture in one universal host; this concentrates it in the fiber structure of local decoders.
artifacts:
  - research/artifacts/gottschalk-decoder-fibers-2026-09-07.md
---

For every finitely generated infinite group G, finite nonempty alphabet
A, and injective cellular automaton tau:A^G -> A^G, there exist a
cellular decoder sigma with sigma tau=id and a configuration z with
dense G-orbit for which sigma^(-1)(z) is at most countable.

This is an OPEN proposed bridge, not a consequence of compactness.
Compactness supplies a decoder but no fiber-size bound. Together with
split-decoders-have-generic-cantor-fibers this criterion is equivalent to
Gottschalk's conjecture, not a weakening known to hold universally.

## Attempts

The finite-collision argument proves that a strict encoder makes EVERY
local decoder have an uncountable fiber over EVERY transitive output.
It therefore cannot construct the countable fiber required here.

Counting 2^n alternatives in n bounded regions supplies no contradiction
to the number of full-shift patterns on those regions. No missing volume
comparison has been established for an arbitrary group.

Passing to the Bernoulli measure pushed through the section also fails:
uncountable topological fibers can have point-mass conditional measures.
Section 7's rectangular projection is an explicit counterexample to that
measure inference, while leaving this equal-alphabet claim unresolved.

The guard construction does not provide a cellular choice of packing
centers or an embedding of an extra full alphabet. Neither extra step may
be assumed when trying to remove the present prerequisite.
