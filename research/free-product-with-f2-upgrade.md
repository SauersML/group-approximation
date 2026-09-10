---
rg: 2
id: free-product-with-f2-upgrade
kind: claim
title: Free-producting with F2 adds C*-simplicity and kills property (T) while preserving every subgroup-closed failure
---

Let `H` be any nontrivial countable group and put `G = H * F_2`.  Then:

* `G` is C*-simple with a unique tracial state, hence has trivial amenable
  radical.
* `G` does not have property (T), and does not have the Haagerup property
  either, unless `H` does.
* `G` inherits from `H` the failure of **every** subgroup-closed property.  In
  particular if `H` is non-sofic, non-MF, non-hyperlinear, non-LEF, non-LEA,
  non-amenable, non-linear, or has torsion, then so does `G`.
* `G` is finitely generated if `H` is, finitely presented if `H` is, and has
  solvable word problem if `H` does.

The point is that C*-simplicity is **free**: it can be bolted onto any example
at no cost to the approximation-theoretic content.  Two directions of use.

* **Constructive.**  Any non-MF or non-sofic example can be upgraded to a
  C*-simple one without touching the argument that produced it.  A construction
  is never obstructed by needing its output to be C*-simple.
* **Negative.**  C*-simplicity carries no information about MF-ness or
  soficity, in either direction.  A proof strategy that hopes to extract an
  approximation obstruction *from* C*-simplicity, or from triviality of the
  amenable radical, cannot work: both are attainable by a construction that is
  blind to `H`'s approximation properties.

The second point is worth keeping in view because the amenable radical is a
recurring handle in this program.  This says the radical being trivial is not
by itself evidence about the MF radical.
