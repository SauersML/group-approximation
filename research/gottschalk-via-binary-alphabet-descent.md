---
rg: 2
id: gottschalk-via-binary-alphabet-descent
kind: route
title: Descend any strict automaton to two symbols and use binary surjunctivity
target: gottschalk-surjunctivity-conjecture
requires:
  - surjunctivity-failure-descends-to-binary-alphabet
  - every-group-is-binary-surjunctive
artifacts:
  - research/artifacts/boolean-core-alphabets-and-network-coding-2026-09-12.md
---

Suppose some group carries an injective non-surjective automaton over some finite alphabet. The
descent claim gives such an automaton over two symbols. That contradicts binary surjunctivity, so
every group is surjunctive over every finite alphabet.

Both prerequisites are open. The route records that the conjecture reduces to the binary alphabet
exactly when strictness descends.
