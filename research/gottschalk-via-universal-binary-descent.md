---
rg: 2
id: gottschalk-via-universal-binary-descent
kind: route
title: Pass from any strict automaton to a binary strict automaton over some group and use binary surjunctivity
target: gottschalk-surjunctivity-conjecture
requires:
  - some-nonsurjunctive-group-gives-a-binary-one
  - every-group-is-binary-surjunctive
artifacts:
  - research/artifacts/gk3-alphabet-descent-2026-09-14.md
---

Suppose some group is not surjunctive over some finite alphabet. The first prerequisite gives a group that is
not surjunctive over two symbols, which contradicts the second. So every group is surjunctive over every
finite alphabet.

Both prerequisites are open. This route asks for less descent than `gottschalk-via-binary-alphabet-descent`,
because the binary witness may live on a different group. By `ec-groups-share-the-nonsurjunctive-alphabet-sizes`
the first prerequisite is binary descent for existentially closed groups.
