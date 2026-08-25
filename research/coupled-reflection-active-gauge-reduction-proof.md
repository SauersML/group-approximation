---
rg: 2
id: coupled-reflection-active-gauge-reduction-proof
kind: route
title: Apply Schur normal form and tensor every residual gauge model back into the packet
target: coupled-reflections-reduce-to-the-active-gauge-profile
requires:
  - fixed-packet-correction-retains-multiplicity-gauge
  - packet-dressed-shared-implementer-requires-one-outer-class
  - fixed-d8-holonomy-has-no-determinant-density
  - hyperlinear-fiber-cannot-orient-btb-return
---

Exactify the finite packet and apply Schur's lemma to every normalizer letter,
obtaining `(CGR1)`.  Multiplication separates each word into a fixed outer
matrix and a multiplicity word.  A relator's outer matrix must be scalar on
the irreducible packet type, leaving `(CGR2)`.  Tensoring any exact or
asymptotic model of those equations with the outer packet proves the
falsification statements.  The controlled and identity-outer occurrences
give `(CGR3)`, so their product is literal controlled reflection exactly when
the residual word `VA` is one.

