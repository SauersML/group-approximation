---
rg: 2
id: three-chart-loop-multiplicity-gauge-proof
kind: route
title: Compute the loop conjugacy invariant and insert an arbitrary spectator unitary
target: three-chart-loop-retains-free-multiplicity-holonomy
requires:
  - two-sl3-shell-charts-have-a-rotated-flip-escape
  - finite-projective-sector-groupoids-have-conjugate-absorbers
---

# Compute the loop conjugacy invariant and insert an arbitrary spectator unitary

Successive use of `(BGL1)` shows that `(BGL2)` has source and range projection
`P_i^0`.  The intermediate gauges cancel telescopically, proving `(BGL3)`.
For two such corner unitaries, expansion of the squared norm of their
difference and their average gives `(BGL5)` and `(BGL6)`.

On a common multiplicity amplification, `1 tensor W` commutes with every
chart projection and every label actor.  Inserting it on one edge therefore
preserves every source, range, covariance, and local inverse equation, while
it multiplies the closed return by `W`.  The rotated-coordinate charts
`(BGL7)` make this construction explicit for the forty-two-point SL3 shell.
Conjugate doubling handles any finite projective label factor independently.

Finally, normalized traces of finite-dimensional unitaries fill a dense
subset of the closed unit disk: approximate a convex combination of points
on the unit circle by rational weights and use a diagonal unitary with those
eigenvalue multiplicities.  Hence no uniform restriction on `(BGL5)` follows
from the chart and transporter axioms alone.
