---
rg: 2
id: spherical-relation-pattern-divisibility
kind: claim
title: Relation-quadruple pattern counts and matching divisibility for the spherical candidate hypergraph
---

After the fixed-order cap intersection estimates are available, prove the
remaining finite sampling statement for the coloured relation hypergraph of
`spherical-candidate-hypergraph-quasirandom`:

1. for every tested relation `gh=k`, the rooted counts of quadruples
   `(i,j,l,m)` satisfying the three radius-one transition constraints have the
   required nearly uniform one-slot degrees, simultaneously over all colours;
2. all repeated-slot/codegree patterns not already reduced to intersections of
   distinct word caps are controlled at the scale required by the eventual
   simultaneous matching theorem; and
3. choose the cloud size / finite reservoir padding so that the finite
   partite-divisibility conditions of that matching theorem hold exactly.

The point of this node is to isolate what remains after
`spherical-fixed-order-cap-codegrees`: **no further higher trace moments are
allowed as an input**.  It is a finite random-point-cloud pattern-counting and
integer-balancing problem.  The coupled matching/absorption itself remains the
separate node `hypergraph-absorption-schreier-matching`.
