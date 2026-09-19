---
rg: 2
id: matrix-corona-projection-monoid-is-rank-germs-proof
kind: route
title: Lift projections and partial isometries and compare their coordinate ranks
target: matrix-corona-projection-monoid-is-rank-germs
requires:
  - matrix-corona-product-k0-is-rank-bounded-sequences
artifacts:
  - GroupApproximation/Analysis/CoronaProjectionLifting.lean
---

Spectral rounding lifts every projection in `M_k(Q_d)` to genuine coordinate
projections `p_n in M_(k d_n)`.  Two such lifts differ by a norm-null
sequence.  Once their distance is below one, each range injects into the
other under the opposite projection, so their ranks agree.  Thus the rank
germ is well defined.

If stable projections are Murray--von Neumann equivalent, lift an
implementing partial isometry.  Its initial and final projection defects tend
to zero.  Polar correction on the spectral subspace above `1/2` produces,
at every sufficiently late coordinate, a genuine partial isometry between
the lifted ranges.  Their ranks are therefore eventually equal.  The same
argument for subequivalence gives eventual rank inequality.

Conversely, eventual equality of coordinate ranks supplies coordinate
unitaries carrying one range to the other.  Eventual inequality supplies
coordinate isometries from the smaller range into the larger.  These bounded
sequences descend to the required corona equivalence or subequivalence.

Every rank sequence bounded by one fixed multiple of `d_n` is realized by
diagonal coordinate projections at that stabilization size.  Block sum is
coordinate rank addition, proving the ordered-monoid isomorphism.

Cancellation and conicality are coordinatewise.  If `[r_n]=[2r_n]`, then
`r_n=2r_n` eventually, so `r_n=0` eventually.  A sequence of projections is
norm-null exactly when it is eventually zero, proving faithfulness.

