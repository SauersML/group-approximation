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

The guard construction does not provide an embedding of an extra full
alphabet, and such an embedding would fail on constant configurations. It
may not be assumed when trying to remove the present prerequisite. A cellular
choice of packing centers *is* available (2026-09-12): a marker rule selects
disjoint guard occurrences locally. It yields infinitely many cellular
sections and an injective equivariant map from a decorated subshift
`Y ⊋ A^G x {0}` into `A^G` (`strict-split-decoders-have-infinitely-many-sections`).
Over an amenable group that embedding contradicts entropy monotonicity. Over a
general group no monotone invariant is known.

*Equivalence recorded (2026-09-12).* The converse route
`countable-transitive-decoder-fiber-from-gottschalk` derives this claim from the
goal, so proving or refuting it is exactly as hard as Gottschalk's conjecture.

*Equivariant measure repair (2026-09-12).* A measurable, factor-of-iid choice of
packing centers is available where a cellular one is not. Keep the guard
occurrences whose i.i.d. label is a local minimum, and flip their licensed
collisions on independent fair bits. The result is an invariant lift of uniform
Bernoulli through the decoder with conditional entropy at least
`log 2 / (|A|^|W| |WW^-1|)` at the identity
(`strict-split-pairs-carry-positive-entropy-flip-lifts`). This repairs the
point-mass-conditional defect of the section measure. It does not remove the
prerequisite, since single-site fiber entropy is not contradictory: the XOR
automaton over `Z` lifts uniform Bernoulli with conditional entropy `log 2`
(`xor-lift-of-bernoulli-has-positive-fiber-entropy`). Only a per-site average
contradicts the alphabet bound. Over `F_2` the Ornstein–Weiss block map shows
no average without the section `tau` can work. See
`research/artifacts/decoder-fiber-flip-lifts-2026-09-12.md`.
