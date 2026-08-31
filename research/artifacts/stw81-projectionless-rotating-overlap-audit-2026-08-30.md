# Audit: projectionless rotating-overlap firewall

Date: 2026-08-30

Claim: `stw81-projectionless-rotating-overlap-degeneracy`.

## Algebraic audit

1. The proof never commutes supports from different frames.  Identity
   (RTP1) preserves the order of every factor.  Its two error terms have
   norm at most `epsilon`, giving the stated constant `2epsilon`.

2. If positive elements have product zero, the reverse product is zero by
   adjunction.  This justifies both left multiplications used to obtain the
   four almost-idempotence estimates.

3. The spectral cutoff is legitimate precisely for `epsilon<1/8`, when
   the two intervals in (RTP4) are disjoint.  Projectionlessness then makes
   the cutoff zero or one.  No stable projectionlessness hypothesis is
   needed because every support lies in `D` itself.

4. Total-return contractivity is not assumed.  The two positive pieces
   `a_i=phi_i psi_i(1)` have sum within `epsilon` of one and hence at most
   `(1+epsilon)1`.  Scaling by `(1+epsilon)^(-1)` makes a genuine subunital
   pair whose unit defect is at most `2epsilon/(1+epsilon)`.

5. Dropping the small return colour costs at most the norm of its returned
   unit piece.  The composition `phi_i psi_i` is positive, so its map norm
   equals the norm of its value `a_i` at the unit.  Thus (RTP7) is uniform
   on the unit ball.  The remaining incoming coordinate and outgoing map
   are c.p.c., and the outgoing map is order zero.

6. At a scalar overlap, exact order zero of a global colour gives exact
   orthogonality after evaluation.  The nonzero scalar cutoff product can
   be cancelled numerically.  The local frames can vary arbitrarily; no
   endpoint conjugator, logarithm, or continuous choice is required.

## Relation to the rotating compression escape

The remote node `stw83-rotating-order-zero-compression-escapes-circle-gap`
shows that compression of one rotating matrix order-zero map by a
noncommuting rank-one corner can approximate a circle unitary.  That does
not contradict this result: such a compression is not order zero and does
not furnish two complete near-unital fibre frames with matched exact
cross-orthogonality.  The present firewall therefore targets the remaining
natural interval construction without asserting rigidity for arbitrary
noncommuting compressions.

## Exact scope

This is a no-go theorem for scalar-localized, indivisible outgoing colours
whose local fibre factorizations are each nearly unital.  It permits exactly
the piecewise contractivity in the definition of nuclear dimension; the
sum of the return colours may have norm two.  It is not a lower bound for
`dim_nuc(C([0,1]) tensor Z)`.  Three escapes remain explicit: share the unit
between neighboring patches so neither local frame is near-unital,
split/refine return colours before global reuse, or mix the patches in the
incoming map.  Hence the theorem sharpens the construction frontier without
claiming to settle STW Problem LXXXI.

Outcome: **PASS**.
