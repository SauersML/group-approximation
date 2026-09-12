---
rg: 2
id: atlas-singular-counting-via-bounded-pure-polar-copies
kind: route
title: Prove Atlas singular counting by boundedly repeating the residual polar slots
target: atlas-six-row-singular-counting-dominates-nontrivial-s3
requires:
  - atlas-affine-collision-collapses-pure-polar-copies
---

**INVALIDATED.**  The proposed repair of the failed principal-angle route
was to replace each initial/final residual high space by boundedly many
labelled copies and apply bounded postprocessings before taking their direct
sum.  On the exact affine frame,
`atlas-affine-collision-collapses-pure-polar-copies` proves
that every such component factors through one half-rank map `QP`.  All
copies retain a common kernel of dimension at least `d/4` (raw orbit size
three) or `3d/8` (raw orbit size six).

Consequently neither repetition, relabelling of initial versus final slots,
nor postprocessing can establish the required injection.  The only surviving
bounded-congestion variant must specify genuinely distinct external
pretransports `Q_r W_(r,j)P`; merely multiplying after `Q_rP` is ruled out.
