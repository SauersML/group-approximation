---
rg: 2
id: gottschalk-specializes-to-three-factor-class
kind: route
title: Apply Gottschalk's assertion to three-factor automata over the same group
target: three-factor-finite-alphabet-ca-are-surjunctive
requires:
  - gottschalk-surjunctivity-conjecture
artifacts:
  - research/artifacts/three-factor-audit-and-controlled-feedback-2026-09-12.md
---

A three-factor automaton is a cellular automaton on the full shift
`(R^N)^G`, whose alphabet is finite. So the universal conjecture applies to it
directly.

**This route closes a cycle on purpose.** With
`stable-three-factor-reduction-proves-gottschalk` it forms a two-route cycle,
and the cycle carries the content: group by group, the three-factor claim and
Gottschalk's assertion for all finite alphabets are equivalent. The
three-factor class is a normal form of the whole conjecture, like 3-SAT for
SAT, not a smaller problem. Theorems about subclasses of it exclude parts of
the conjecture and do not reduce it. Do not delete either route to silence the
cycle warning; both implications are true.

The independent re-derivation of the stable reduction is section 1 of the
linked artifact.
