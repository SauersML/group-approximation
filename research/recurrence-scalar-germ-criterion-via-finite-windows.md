---
rg: 2
id: recurrence-scalar-germ-criterion-via-finite-windows
kind: route
title: Combine the forward recurrence lattice with finite-window HNN stabilization
target: recurrence-scalar-germ-fp-iff-recurrent
requires:
  - integer-recurrence-tails-have-finite-forward-lattices
  - finite-window-metabelian-hnn-stabilizes
artifacts:
  - research/artifacts/beyond-polynomial-germs/recurrence-and-matrix-proofs.md
---

The first prerequisite makes the germ semidirect product an actual
injective ascending HNN extension of finite-rank free abelian `L`, so
recurrence implies `F_∞`, hence finite presentation. The second forces
finite rational rank from finite presentation. On a finite-dimensional
shift-invariant rational space, Cayley–Hamilton gives a recurrence for
each profile. Conversely recurrences give finite-dimensional rational
shift spans. Section 4 checks the arithmetic germ representation by
annular exponent detection and the independent zoom depth character.
Both mathematical prerequisites are unresolved; this conditional route
does not accept the manuscript as a complete proof.
