# Audit: shared-unit two-chart scalar firewall

Date: 2026-08-30

Claim: `stw81-shared-unit-two-chart-patching-forces-af`.

## Checks

1. Two evaluations suffice.  Subtracting the two affine mixtures produces
   exactly `(lambda-mu)(T^0(a)-T^1(a))`; division costs only the fixed
   condition number `kappa^(-1)`.  Substitution into either mixture gives
   the explicit error `epsilon(1+2/kappa)` for each local map.

2. The deconvolution applies to the unit and to arbitrary contractions; it
   does not rely on positivity or commutativity.  Positivity enters only
   afterwards, for the returned unit pieces.

3. Ordinary nuclear-dimension conventions are respected.  Each outgoing
   colour is c.p.c. order zero, but their sum may have norm two.  The proof
   scales the returned unit pieces, not the outgoing maps, before applying
   the subunital near-partition lemma.

4. Orthogonality of the full outgoing ranges implies orthogonality of the
   returned unit pieces.  In the scalar interval model, evaluation at one
   point where both cutoffs are nonzero cancels the positive scalar product
   and supplies this exact range orthogonality.

5. The colour which is small at the unit is small as a map after composing
   incoming and outgoing maps: a positive map has norm equal to the norm of
   its value at the unit.  Dropping it therefore gives a genuine
   one-colour finite-dimensional approximation.

6. In the fixed-anchor corollary, each local returned unit has norm at most
   two because it is the sum of two positive contractions.  The difference
   of the endpoint outputs on `id tensor 1` is the cutoff oscillation times
   `x_0A-x_1B`, whose norm is at most two.  Approximating zero and one at
   the two endpoints therefore forces the uniform oscillation bound
   `(1-2epsilon)/2`; asymptotically constant cutoffs cannot approximate the
   base coordinate.

## Boundary

The lower bound on the oscillation of the scalar cutoff is essential in the
abstract theorem.  If it tends to zero with the approximation tolerance,
the two-by-two scalar system becomes ill-conditioned and does not recover
either local map.  The fixed-anchor corollary shows that flattening is not
available in the standard evaluation construction because the base
coordinate detects it.  More importantly, the theorem assumes the two
fibre factorizations are fixed across the transition.  A base-dependent
incoming map or a subdivision of the outgoing maps does not have the affine
form (SUT6).  Those are exactly the constructive escapes left open.

No assertion about the actual value of
`dim_nuc(C([0,1]) tensor Z)` is made.

Outcome: **PASS**.
