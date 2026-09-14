---
rg: 2
id: residually-finite-groups-are-surjunctive
kind: claim
title: Every residually finite group is surjunctive
distinct_from:
  rf-lamp-wreaths-over-surjunctive-bases-are-surjunctive: that is a permanence theorem producing surjunctive groups that need not be residually finite or sofic; this is the classical base case for residually finite groups.
---

Let `G` be a residually finite group and `A` a finite alphabet. Every
injective cellular automaton `A^G -> A^G` is surjective.

Classical (Lawton). References:
* Ceccherini-Silberstein--Coornaert, *Cellular Automata and Groups*,
  Section 3.3.
* The attribution in Seward, arXiv:1501.03367v4, Section 1.

The proof: `N`-periodic configurations for finite-index normal subgroups `N`
are finite invariant sets on which injectivity forces bijectivity. They are
dense, and the image of an automaton is closed.

Gromov and Weiss extend this to all sofic groups. That extension is not needed
here.
