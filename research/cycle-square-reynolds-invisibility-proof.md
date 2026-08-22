---
rg: 2
id: cycle-square-reynolds-invisibility-proof
kind: route
title: Retune one chord in the commutant and conjugate the Reynolds average
target: cycle-holonomy-is-square-gauge-and-reynolds-invisible
requires:
  - oracular-local-block-detectors-miss-balanced-cycle-holonomy
  - central-square-orients-transverse-ledger
  - reynolds-rank-gap-forces-hs-holonomy-energy
---

An intertwiner `T:H_x->H_y` between two copies of `rho` remains an
intertwiner after right multiplication by any unitary in `rho(F)'` on the
source.  After the tree edges have been gauged, each chord is the unique edge
of its fundamental cycle not in the tree.  Right multiplication on that edge
therefore changes the corresponding cycle product by an arbitrary
commutant unitary and does not alter any local packet relation.  Taking the
new product to be `I` or `iI` proves the square-clause assertion.

For Reynolds invisibility, `V rho(f)=rho(f)V` implies
`Ad(V)Ad(rho(f))=Ad(rho(f))Ad(V)` term by term.  Averaging and using that
`R_F` is the orthogonal projection onto the packet commutant gives `(CHR4)`.
Every context Reynolds projection is a conjugate of `R_F`; composing around
the cycle leaves only `Ad(V)`, which fixes it.  Hence the cycle comparison
has exactly zero energy, independently of matrix size and monodromy.
