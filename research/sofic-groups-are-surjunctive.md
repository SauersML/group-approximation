---
rg: 2
id: sofic-groups-are-surjunctive
kind: claim
title: Every sofic group is surjunctive
distinct_from:
  residually-finite-groups-are-surjunctive: that is the classical residually finite base case due to Lawton; this is the Gromov--Weiss theorem for all sofic groups, which contains it.
  sofic-radical-localizes-garden-of-eden-windows: that localizes the Garden-of-Eden windows of an injective automaton on an arbitrary group to its sofic radical; this is the classical theorem for sofic groups, which that node recovers when the radical is trivial.
---

Let `G` be a sofic group and `A` a finite alphabet. Every injective cellular
automaton `A^G -> A^G` is surjective.

This is due to Gromov (1999) and Weiss (2000). The proof counts patterns along
sofic approximations. `sofic-radical-localizes-garden-of-eden-windows` runs the
same count along almost-multiplicative permutation models of an arbitrary group.

It is the base case of the dead route
`fixed-host-surjunctive-via-sofic-permanence`.
