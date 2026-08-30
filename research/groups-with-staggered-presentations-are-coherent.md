---
rg: 2
id: groups-with-staggered-presentations-are-coherent
kind: claim
title: Every group with a staggered presentation is coherent
distinct_from:
  one-relator-groups-are-coherent: one-relator presentations form a special case; this theorem also covers multi-relator and infinite staggered presentations.
  magnus-staggered-chain-sofic: that asks for finite permutation approximations of a particular infinite staggered Magnus chain and remains open; coherence only says its finitely generated subgroups are finitely presented.
  one-relator-groups-sofic: coherence does not imply soficity and leaves Pestov Question 4.10 open.
---

Let `G` admit a staggered presentation in the sense of Jaikin-Zapirain--Linton
Section 2.5: the two-cells and a distinguished set of one-cells are ordered,
every attaching map traverses a distinguished one-cell, and the minimum and
maximum traversed distinguished edges increase strictly with the two-cell
order. Then `G` is coherent: every finitely generated subgroup of `G` is
finitely presented.

The presentation may be infinite, may mix proper-power and non-proper-power
relators, and need not define a torsion-free or virtually torsion-free group.
This settles Wise's Conjecture 14.10.

**ESTABLISHED 2025** by
[[jaikin-linton-staggered-presentation-coherence-proof]].
