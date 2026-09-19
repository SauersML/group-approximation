---
rg: 2
id: shared-bcs-eight-slice-symmetric-return
kind: claim
title: Return the symmetrized actual-failure orbit through one shared BCS capacity cell
distinct_from:
  s3-equivariant-endpoint-conventions-use-global-bcs-words: that asks the one holonomy to realize the original rank-one no-signaling endpoint marginals directly; this uses finite bookkeeping replication to equalize the three actual failure projections before the return.
  globally-conditioned-v4-exit-capacity: that routes the unequal unamplified five-fourths sources; this routes one equal-rank S3 orbit with source-to-parent ratio three-halves.
  exact-five-fourths-projection-return-collapses-the-packet: that rules out literal group-algebra compression; this requires a finite-matrix-only decoded return and permits a properly infinite exact witness.
---

OPEN.  For every context of the fixed shared Fanizza BCS, apply the
eight-slice construction and write

```text
G_(c,b),       b in {00,01,11},       C_c=P_c tensor d_4. (SBR1)
```

Use `regular-induced-affine-reset-synchronizes-s3-holonomy` and the finite
monomial symmetry of `(ESB3)` to expose the three sources as one equivariant
orbit.  Construct, only in finite-dimensional microstates after simultaneous
packet exactification, partial isometries `T_(c,b)` such that

```text
T_(c,b)^*T_(c,b)=G_(c,b),
sum_(c,b)||(1-C)T_(c,b)||_2^2
 +sum_((c,b)!=(c',b'))||T_(c,b)^*T_(c',b')||_2^2
 <= K E_rel+o(1),                                      (SBR2)
```

where `C=directSum_c C_c` and `E_rel` is a bounded-overlap energy formed
from the original shared BCS words before the context copies are separated.
The construction must admit a countably amplified exact marked
representation, with properly infinite multiplicity allowed.

The analytic conclusion is immediate.  The Gram-capacity inequality and
`(ESB4)` give

```text
K E_rel+o(1) >= sum_(c,b)tau(G_(c,b))-tau(C)
              =(1/2)tau(C)
              =(1/16)sum_c tau(P_c).                  (SBR3)
```

Together with the robust Fanizza BCS gap, `(SBR3)` yields a fixed
finite-dimensional energy floor.  The semantic problem left by the unequal
`00,01,11` ranks is no longer present: every source in `(SBR2)` is an actual
failure event and all three have the same finite packet type.

The remaining return must still use genuinely global contextual operator
data.  Independent contextwise returns, or a literal conjugacy into `C`,
would be valid in the regular representation and collapse the embedded
packet.  Candidate implementations are a packet-compressed Toeplitz cell, a
shared cross-Gram tag extracted from the original BCS tuple, or an adjoint
scalar-overlap actuator.  This is now the only non-finite step in this lane.

The bookkeeping characters do not secretly solve this step.
`finite-tag-covariance-cannot-compress-eight-slice-orbit` proves that exact
covariance for pairwise disjoint finite tags forces their target ranges to be
orthogonal and therefore forces target dimension at least the summed source
dimension.  The matrix-only return must exploit the shared non-CE tuple or a
one-sided actuator; it cannot be obtained by merely promoting the book bits
to finite tag types.

A strictly weaker sufficient replacement is now isolated as
`shared-bcs-eight-slice-full-overlap-actuator`.  Because the three sources are
orthogonal, their sum is one projection `S`; the entire capacity deficit is
the single scalar `tau(S)-tau(SW^*CWS)`.  The one-overlap route goes directly
to fixed-scale holonomy and does not need to construct the partial
isometries demanded in `(SBR2)`.

There is also a precise multi-square version.
`compressed-k2m-locks-gauge-but-needs-matrix-separator` puts the three sources
in the columns of `K_(2,3)`. Its two rectangle holonomies remove the last
multiplicity gauge and prove

```text
tau(P_f)/16<=2(ell+h),
```

where `h` is ordinary rectangle-word energy and `ell` is the compressed
row-one leakage into the parent capacity. Thus multi-square synchronization
is sufficient once the shared non-CE tuple supplies `ell<=K E_rel+o(1)`.
Rectangles alone are insufficient, and making the leakage a universal
reflection relator contradicts the regular trace. The remaining input is
still genuinely matrix-only, but no additional gauge-locking theorem is
needed.
