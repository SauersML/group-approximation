---
rg: 2
id: perfect-commuting-unique-game-is-classically-satisfiable
kind: claim
title: Every perfect commuting strategy for a unique game yields a perfect classical labeling
distinct_from:
  functional-support-is-affine-exactly-on-an-affine-domain-map: that classifies affine safety of a single functional support; this rules out the stronger permutation/unique-game source as a perfect-versus-finite gap even before affine lowering.
  oracularizable-tracial-nonru-game-exists: that gives a perfect commuting finite-gap game with general constraint relations; this shows why those relations cannot all be unique constraints.
---

**ESTABLISHED UNIQUE-GAME PERFECTNESS COLLAPSE.**  Let `G` be a finite
two-player unique game: on every question edge `(x,y)`, acceptance is

```text
b = pi_xy(a),
```

where `pi_xy` is a permutation of the answer alphabet.  If `G` has a perfect
commuting-operator strategy, then `G` has a perfect deterministic classical
strategy.  Consequently no unique game can have perfect commuting value one
and finite-dimensional quantum value strictly below one.

The statement is exact and does not use a quantitative rounding theorem.
Zero loss makes the state-vector pieces carrying an answer at one endpoint
equal to the pieces carrying its uniquely determined answer at the other
endpoint.  A nonzero piece can therefore be transported around the question
graph.  Orthogonality forces every cycle permutation to fix its transported
label, so the labels obtained by path transport form a globally consistent
classical assignment.

This closes the unique/permutation branch of the search for an affine-safe
perfect-gap verifier.  The positive binary-functional exception in
`functional-support-is-affine-exactly-on-an-affine-domain-map` cannot be
reached by taking a unique game: perfect completeness there already gives a
finite perfect model.  The CMPS smooth-label-cover construction must use
non-unique projection fibers, and those fibers retain the active-domain
affine-safety problem.
