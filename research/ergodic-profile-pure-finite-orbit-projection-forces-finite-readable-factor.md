---
rg: 2
id: ergodic-profile-pure-finite-orbit-projection-forces-finite-readable-factor
kind: claim
title: On an ergodic ZPC witness a profile-pure finite-orbit projection is equivalent to finite readable closure
distinct_from:
  perfect-gap-zpc-has-finite-readable-translate-algebra: that asks for finite closure on a selected gap witness; this shows that replacing it by one positive profile-pure finite-orbit projection does not weaken it after choosing the witness ergodic.
  finite-invariant-partition-only-reduces-irs-to-fiber-irs: that analyzes what a finite invariant partition does to the stabilizer character; this is the measure-theoretic equivalence which produces that partition.
  finite-depth-readable-groupoid-closes-iff-full-orbit-is-finite: that compares finite-depth normalization with full orbit finiteness; this starts from one positive set whose entire finite orbit remains profile-pure.
---

Let `Q_G` act ergodically on the `J`-quotient of a ZPC-IRS realization,
and let `D_0` be its finite joint readable-profile algebra.  The following
are equivalent.

1. The full readable translate algebra
   `D_infinity=W*(g D_0 g^(-1):g in Q_G)` is finite dimensional.
2. There is a positive-measure set `A` such that its `Q_G`-orbit is finite
   and every translate `gA` is contained modulo null sets in one atom of
   `D_0`.

Thus the NONHALT compactness witness does not acquire a genuinely weaker
escape hatch by asking only for one nonzero `D_0`-profile-pure projection
with finite `Q_G` orbit.  On the ergodic witness available from
`perfect-zpc-irs-quantum-gap-game`, such a projection already forces the
entire readable factor to be finite.
