---
rg: 2
id: separate-packet-common-matching-no-go-proof
kind: route
title: Haar-average the independent multiplicity gauges
target: separate-packet-calculi-have-no-common-matching
requires:
  - packet-natural-selectors-cannot-extract-one-bounded-copy
  - canonical-finite-packet-data-stop-at-scalar-overlaps
---

On each irreducible finite-packet carrier, Schur's lemma identifies the
packet automorphisms with the full multiplicity unitary group.  Since the
two inputs contain no cross-reservoir operator, these automorphism groups act
independently.  Apply naturality to the unchanged input.  The output cuts and
matching must obey `(SPC4)`.  Commutation with every multiplicity unitary
makes each cut scalar, and the sign unitary in either one of the two
independent factors kills the matching.

For the quantitative assertion, expand the two squared Hilbert--Schmidt
norms and Haar-average.  Twirling a projection of normalized trace `t`
gives `tI`, yielding `(SPC5)`.  Independence and zero Haar mean of either
unitary kill the cross term for `J`, yielding `(SPC6)`.  Hence a matching of
fixed normalized mass has fixed gauge-covariance cost even at zero packet
defect.

All listed packet-local selector calculi are unitary functors, so their
outputs satisfy the same covariance equations.  A mixed block transforms
between the two gauges and is the first datum whose polar decomposition can
escape the sign argument, proving the stated boundary.
