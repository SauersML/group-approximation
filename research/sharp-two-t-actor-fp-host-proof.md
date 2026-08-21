---
rg: 2
id: sharp-two-t-actor-fp-host-proof
kind: route
title: Apply the two-orbit permutational-wreath presentation criterion
target: sharp-two-t-actor-gives-fp-host
requires:
  - infinite-character-actor-kills-fd-mark
---

Sharp two-transitivity supplies one orbit of diagonal pairs and one orbit of
distinct ordered pairs.  The standard finite-presentation criterion for a
permutational wreath product with nontrivial finitely presented lamp says
that `C_2^(X) semidirect A` is finitely presented when `A` is finitely
presented, point stabilizers are finitely generated, and the diagonal action
has finitely many orbits.  All hypotheses hold here.  Its augmentation
kernel is index two.

The character argument is elementary.  The dual of the full lamp module is
the coloring space `F_2^X`.  A finite orbit is fixed by simplicity, and
transitivity makes a fixed coloring constant.  A constant coloring takes
the same value at `x,y`, so it evaluates `+1` on
`m_0=delta_x+delta_y`.  Property `(T)` applied to each remaining infinite
quasi-regular orbit gives a uniform gap for one fixed generating set.

The D8-seed extension is finite over the finite presentation.  Its nonzero
infinite model and exact finite-dimensional collapse are those of
`infinite-character-actor-kills-fd-mark`.
