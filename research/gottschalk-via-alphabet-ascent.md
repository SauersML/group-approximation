---
rg: 2
id: gottschalk-via-alphabet-ascent
kind: route
title: Push any strict automaton up to a binary-power alphabet and use surjunctivity there
target: gottschalk-surjunctivity-conjecture
requires:
  - strict-rule-pairs-ascend-to-larger-alphabets
  - every-group-is-surjunctive-over-binary-power-alphabets
  - surjunctivity-is-axiomatized-by-rectangle-clauses
artifacts:
  - research/artifacts/formalizability-prime-fields-and-alphabet-bridge-2026-09-12.md
---

Suppose a group `G` carries an injective non-surjective automaton over `k` symbols.

1. By the third prerequisite, its rules are strict for the tables realized on `G` by its memories.
2. Choose `n` with `2^n >= k`. The first prerequisite gives rules over `2^n` symbols strict for the same
   tables.
3. By the third prerequisite again, these rules give a strict automaton on `G` with the same memories.
4. That contradicts the second prerequisite. So every group is surjunctive over every finite alphabet.

The first two prerequisites are open. The route records that the conjecture reduces to binary-power
alphabets exactly when strictness ascends. It is the ascent counterpart of
`gottschalk-via-binary-alphabet-descent`.
