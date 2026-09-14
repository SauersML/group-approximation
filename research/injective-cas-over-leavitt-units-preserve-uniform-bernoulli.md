---
rg: 2
id: injective-cas-over-leavitt-units-preserve-uniform-bernoulli
kind: claim
title: Every injective cellular automaton over the binary Leavitt unit group preserves the uniform Bernoulli measure
distinct_from:
  leavitt-unit-group-has-positive-rokhlin-entropy-action: that asks for one free ergodic action of positive Rokhlin entropy; this asks that every injective automaton on every full shift preserve the uniform Bernoulli measure.
  leavitt-unit-group-surjunctive: that is the surjunctivity conclusion; this is the measure-preservation sufficient condition that yields it through the full-support lemma.
  injective-measure-preserving-ca-is-surjective: that is the general lemma that measure preservation gives surjectivity; this is the group-specific hypothesis that the preservation actually holds over the Leavitt unit group.
artifacts:
  - research/artifacts/gottschalk-kazhdan-direct-attack-2026-09-12.md
---

**OPEN.** Let `U = L_{F_2}(1,2)^x`. For every finite alphabet `A`, every
injective cellular automaton `tau: A^U -> A^U` preserves the uniform Bernoulli
measure `mu_A` on `A^U`.

By `injective-measure-preserving-ca-is-surjective` this implies
`leavitt-unit-group-surjunctive`
(`leavitt-units-surjunctive-via-measure-preservation`). A strict automaton over
`U`, if one existed, would be exactly an injective automaton that fails to
preserve `mu_A`.

## Attempts

- **This is the target the Kazhdan tools must hit.** `U` is simple with property
  (T), so the Bernoulli action `U ↷ (A^U, mu_A)` has spectral gap and is strongly
  ergodic. By the direct-attack artifact, spectral gap, strong ergodicity and the
  absence of finite quotients do not detect non-surjectivity on their own, because
  a measure-distorting injective automaton is not a measure-preserving
  transformation and its proper closed image is invisible to invariants of the
  measure-preserving dynamics. They contribute only if used to force this
  preservation. No such argument is known.
- **Relation to Rokhlin entropy.** Preservation of `mu_A` by every injective
  automaton is the qualitative form of maximal Bernoulli Rokhlin entropy over
  `U`; the quantitative route is `positive-rokhlin-entropy-makes-leavitt-units-surjunctive`
  through `leavitt-unit-group-has-positive-rokhlin-entropy-action`. No lower bound
  on Rokhlin entropy for `U` is known without sofic models, and `U` has full sofic
  radical (`sofic-radical-localizes-garden-of-eden-windows`).
- **Linear automata.** For a linear automaton the statement is direct finiteness
  of `F_2[U]`: a strict linear automaton is a one-sided inverse in a matrix ring
  over `F_2[U]` (`stable-finiteness-failure-refutes-surjunctivity`,
  `leavitt-stable-finiteness-equals-direct-finiteness`), which fails to preserve
  the counting-additive structure the uniform measure sees. This special case is
  itself open.
