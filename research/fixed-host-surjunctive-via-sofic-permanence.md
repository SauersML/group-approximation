---
rg: 2
id: fixed-host-surjunctive-via-sofic-permanence
kind: route
title: Prove the tester host surjunctive by iterating the permanence theorems from sofic groups
target: fixed-gottschalk-test-group-is-surjunctive
requires: [fixed-host-lies-in-sofic-permanence-closure, sofic-groups-are-surjunctive, finitary-split-extension-surjunctivity-permanence, graph-folds-over-surjunctive-groups-are-surjunctive, lef-lamp-graph-wreaths-are-surjunctive]
---

**Dead.** Invalidated by `fixed-host-outside-sofic-permanence-closure`.

The implication is valid:
- Gromov--Weiss gives the base case;
- the three permanence theorems carry surjunctivity through their
  constructions;
- subgroup and directed-colimit permanence are Sections 1--3 of
  `gottschalk-surjunctivity-fixed-tester-proof`.

Transfinite induction over the construction of `S_0` then makes every member
surjunctive. The first prerequisite, however, is false.
