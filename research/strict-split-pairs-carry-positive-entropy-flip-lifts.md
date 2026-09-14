---
rg: 2
id: strict-split-pairs-carry-positive-entropy-flip-lifts
kind: claim
title: A strict split automaton pair carries an invariant lift of uniform Bernoulli with positive fiber entropy
distinct_from:
  split-decoders-have-generic-cantor-fibers: that embeds Cantor sets in topological fibers and records that the section measure has point-mass conditionals; this builds a different invariant lift of the same output law whose conditional entropy is positive, the measure an entropy argument consumes.
  injective-ca-admit-countable-transitive-decoder-fiber: that is the open countable-fiber criterion, equivalent to the goal; this is an established measure-theoretic consequence of strictness.
artifacts:
  - research/artifacts/decoder-fiber-flip-lifts-2026-09-12.md
---

Let `G` be a countable group, `A` a finite alphabet, and `lambda` the uniform
Bernoulli measure on `A^G`. Let `tau, sigma` be cellular automata on `A^G` with
`sigma tau = id` and `tau sigma != id`. Let `W` be the guard window of
`split-decoders-have-generic-cantor-fibers`.

Then there is a `G`-invariant Borel probability measure `nu` on `A^G` with

    sigma_* nu = lambda,        (tau sigma)_* nu = tau_* lambda,
    H_nu( x(e) | sigma^-1(Borel) ) >= log 2 / ( |A|^|W| |W W^-1| ) > 0.

Moreover `nu` is a block factor of an i.i.d. process.

*Construction.* Start from `tau(z)` with `z ~ lambda`. At each guard occurrence
whose i.i.d. label is a strict local minimum among the labels of the
overlapping occurrences, flip the licensed finite collision on an independent
fair coin. The chosen occurrences are pairwise disjoint, so every flip keeps the
`sigma`-image equal to `z`. Given `z` and the labels, the flipped sites carry
independent fair bits. Full proof: Section 3 of the artifact.

Over an amenable group, averaging this bound over Følner sets contradicts the
alphabet bound, which recovers the classical theorem. Over a nonamenable group
the single-site bound is not contradictory by itself:
`xor-lift-of-bernoulli-has-positive-fiber-entropy`.
