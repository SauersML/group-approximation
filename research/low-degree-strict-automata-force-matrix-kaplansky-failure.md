---
rg: 2
id: low-degree-strict-automata-force-matrix-kaplansky-failure
kind: claim
title: A strict automaton over F_q with deg sigma * deg tau below q forces a matrix direct-finiteness failure of F_p over the group
distinct_from:
  stable-finiteness-failure-refutes-surjunctivity: that is the converse direction, a matrix one-sided pair gives a strict linear automaton; this asks that every low-degree strict automaton come from such a pair.
  low-degree-strict-pairs-have-one-sided-linear-parts: that is the established dichotomy, a pair or a unipotent automaton; this is the open statement that the unipotent branch never yields a strict automaton without a pair.
artifacts:
  - research/artifacts/low-degree-strict-pairs-linear-parts-2026-09-12.md
---

**OPEN.** Let `G` be a group and `F = F_q` with `q = p^k`. Suppose `G` carries an injective,
non-surjective automaton `tau` over `F^m` with a left inverse `sigma` satisfying
`deg sigma * deg tau < q`. Then `M_n(F_p[G])` is not directly finite for some `n`.

**Why it matters.** It would say that low-degree nonlinearity over large fields never produces
a counterexample beyond the linear Kaplansky ones. Every search for nonlinear designs could then
restrict to degree products at least `q`, where the reduction `x^q = x` is essential to the
decoder identity.

## Attempts

- **Route.** `low-degree-kaplansky-failure-via-unipotent-surjectivity`. The established
  dichotomy leaves only the unipotent branch. That branch is harmless exactly when
  `unipotent-automata-over-finite-fields-are-surjective` holds.
- **Without the unipotent claim.** A strict unipotent automaton has invertible linear part.
  Nothing in its linear data carries a pair, so this needs a genuinely nonlinear argument.
  None is known.

Sections 2 and 5 of the artifact.
