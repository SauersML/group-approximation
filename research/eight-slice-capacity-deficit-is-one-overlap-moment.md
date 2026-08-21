---
rg: 2
id: eight-slice-capacity-deficit-is-one-overlap-moment
kind: claim
title: The equal-rank S3 return is certified by one scalar overlap moment
distinct_from:
  global-v4-exit-capacity-is-cross-gram-curvature: that uses one partial isometry per unequal V4 failure occurrence and sums leakage plus all cross-Gram entries; this uses the orthogonal equal-rank bookkeeping source and one actuator compression.
  schur-reynolds-one-overlap-actuator: that measures an adjoint Reynolds rank gap on the full matrix Hilbert space; this is an ordinary-space overlap between explicit packet spectral projections.
  finite-tag-covariance-cannot-compress-eight-slice-orbit: that rules out an exact finite-tag implementation; this identifies the scalar a finite-matrix-only non-finite actuator must force.
---

In the eight-slice packet put

```text
S=G_00+G_01+G_11.                                      (EOM1)
```

The summands are orthogonal, so `S` is a projection and

```text
tau(S)=3 tau(P_f)/16,       tau(C)=2 tau(P_f)/16.      (EOM2)
```

For any unitary `W` define the single scalar

```text
Theta_W=tau(S W^* C W S)=||CWS||_2^2.                 (EOM3)
```

Then

```text
0<=Theta_W<=tau(C),
tau(S)-Theta_W=||(1-C)WS||_2^2.                       (EOM4)
```

Consequently every estimate

```text
Theta_W >= tau(S)-delta                               (EOM5)
```

forces

```text
delta >= tau(S)-tau(C)=tau(P_f)/16.                  (EOM6)
```

Thus a matrix decoder does not need three returned partial isometries, their
pairwise Gram matrix, or copywise multiplicity coordinates.  It is enough to
authenticate one scalar statement saying that one actuator returns the
orthogonal source sum almost entirely into the parent slice.

This scalar is group-word visible after fixed packet exactification.  Both
`S` and `C` are fixed rational linear combinations of words in the commuting
selector, radical, and book involutions.  Expanding `(EOM3)` therefore writes
`Theta_W` as a fixed finite rational linear combination of ordinary moments

```text
tr(u W^* v W u'),                                     (EOM7)
```

with packet words `u,u',v`.  No dimension-dependent projection or spectral
atom is named.  The construction problem is solely to force the lower bound
`(EOM5)` in Connes-embeddable matrix microstates from the shared BCS
relations.

The bound cannot hold in every tracial representation: the canonical group
trace contains the finite packet with positive `P_f`, and `(EOM6)` would
contradict zero relator defect.  Hence a proof of `(EOM5)` must use the
matrix-ultraproduct origin, not merely cyclic trace or exact covariance.
