---
rg: 2
id: signed-hecke-cycle-only-route
kind: route
title: Build the join-tree atlas and close its non-tree chords one at a time
target: simultaneous-block-escaping-context-holonomy
requires:
  - join-tree-bcs-has-explicit-signed-hecke-atlas
  - first-cycle-signed-hecke-chord
---

First split every BCS variable into separate context occurrences.  Choose a
forest of overlap identifications and retain only those occurrence equalities;
the resulting partial system has a join forest (empty-separator edges may be
added to connect its components).  The established input constructs all
context partitions and retained tree-overlap identities.  Every omitted
equality between two occurrences of an original variable is now a chord.

Apply the chord claim successively to those finitely many equalities.  Its
preservation clause keeps the identities already closed, so finite induction
recovers the original shared-variable tuple and produces the simultaneous
context holonomy.
