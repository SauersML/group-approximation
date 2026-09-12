---
rg: 2
id: injective-binary-automata-are-stably-formalizable
kind: claim
title: Every injective binary automaton, after adding identity ancilla tracks, has a left inverse forming a formalizable pair
distinct_from:
  injective-binary-automata-have-formalizable-left-inverses: that asks for a formalizable left inverse on the original alphabet, which fails for one-track non-affine automata on bi-orderable groups; this allows identity ancilla tracks, where components reading the top cell can cancel and the leading-term obstruction no longer applies.
  binary-left-inverse-pairs-are-formalizable: that asks every pair on the original alphabet to be formalizable; this asks only for some left inverse of the stabilized automaton.
  sitewise-pairs-over-prime-fields-are-stably-formalizable: that treats sitewise pairs over prime fields; this asks for every injective binary automaton with arbitrary memory.
artifacts:
  - research/artifacts/formal-polynomial-strict-pairs-2026-09-12.md
---

**OPEN.** For every group `G` and every injective automaton `tau` on `(F_2^n)^G`, there is `m >= 0`
such that `tau x id` on `(F_2^(n+m))^G` has a left-inverse automaton `sigma'`, and representatives
of both with `sigma' o (tau x id) = id` formally. The representatives of the identity on the ancilla
tracks may involve data variables; only the functional identity is fixed.

**Why it matters.** `tau x id` is strict iff `tau` is. So by
`formal-polynomial-strict-pairs-need-unstable-linearization`, this claim makes every group with stably
finite `F_2[G]` surjunctive over every alphabet of size `2^n`, through
`stable-formalization-reduces-surjunctivity-to-kaplansky`.

## Attempts

- **One track is not enough.** Over bi-orderable groups a formalizable one-track binary pair is a
  shift plus a constant: the extreme variable enters `X_1` through one encoder component with degree
  `DE >= 1`, which forces single-cell windows. So the marker involution
  `x_i -> x_i + [x_(i-3..i+3) = 001*100]` on `{0,1}^Z` has no formalizable left inverse on its own
  alphabet (gk-fz-bennett). That refutes the unstabilized claims.
- **Tracks break that argument.** In the track shear `(x, y) -> (x, y + x(g+1) x(g+2))` the top
  variable cancels between components, and the pair is formalizable
  (`structurally-reversible-automata-are-formalizable`).
- **Sitewise pairs over prime fields** are stably formalizable
  (`sitewise-pairs-over-prime-fields-are-stably-formalizable`).
- **First test: the marker involution with one ancilla.** Compute the marker into the ancilla with a
  track shear, flip the data with a linear track shear, then uncompute. The uncompute leaves the
  residue `m_i(x + m(x)) - m_i(x)`. Markers are exclusive functionally, but `F_2[X]` is a domain,
  so `m_i m_(i+k)` is never zero formally, and the residue must be cancelled by other terms.
- **Where it stops.** No ancilla construction is known for any one-track non-affine automaton on a
  bi-orderable group, and no invariant is known that survives cancellation between components.
