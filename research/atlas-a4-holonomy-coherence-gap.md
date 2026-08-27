---
rg: 2
id: atlas-a4-holonomy-coherence-gap
kind: claim
title: Exact regular A4 holonomy networks with collision 19243 beat the S3 energy wall
refuted_by: atlas-multiplicity-two-refutes-holonomy-coherence-gap
distinct_from:
  atlas-two-s3-energy-ceiling-below-19243-floor: that asks for a uniform ceiling for arbitrary sufficiently-small finite atlas models; this claim only concerns the exact-regular context networks produced from the necessity direction of a hypothetical hyperlinear model.
artifacts:
  - research/artifacts/a4-context-virtually-free-compiler-2026-08-19.md
  - experiments/atlas-word-19243.json
  - experiments/atlas_triangle_19243_packet.py
  - experiments/atlas_a4_packet_generation.py
---

**REFUTED.**  The exact multiplicity-two frame, regularized in its finite
generated group, is a constant sequence satisfying the stated regular A8/A4
types, identity stable letters, all packet contexts, and `q_19243=1`.  Its
two raw S3 covariance opcodes are nonidentity order-four elements, so the
regular trace gives `a_n^2+b_n^2=4`.  See
`atlas-multiplicity-two-refutes-holonomy-coherence-gap`.

Let `sigma_n` be exact unitary representations of the fixed thirty-context
A4 graph of groups from `atlas-a4-context-network-simultaneous-hs-exactification`
on spaces of dimension `d_n=20160 k_n`, with the following normalized form:

- each of the two A8 chart vertices is exactly `k_n Reg(A8)`;
- each A4 context vertex is exactly `1680 k_n Reg(A4)`;
- every non-tree stable letter tends to `1` in normalized Hilbert--Schmidt norm;
- the chart-word collision `q_19243` tends to `1`.

Let `h_a,h_b` be the two fixed involutions generating the raw S3 slice used by
`atlas-packet-forces-two-s3-covariance-energy`, and let `a_n,b_n` be their two
chart-to-chart covariance defects in `sigma_n`.  Then

```text
limsup_n (a_n^2+b_n^2) < 1/32.                         (A4-HOL-GAP)
```

Equivalently, the two binary consistency defects satisfy

```text
limsup_n (D_a+D_b) < 1/128.
```

This is the finite-dimensional core left after all local analytic noise and all
representation-type freedom have been compiled away.  The only growing object
is the common multiplicity `k_n`; every local group is exact and regular.

## Attempts

- **Do not propagate scalar character labels.**
  `a4-regular-c3-c2-character-overlap-is-flat` proves that the classical
  character channel of every regular A4 context is exactly rank one, so an
  ordinary stochastic agreement/expansion proof has no signal to amplify.
- **Propagate the matrix-valued coherence fan.**
  `a4-regular-three-way-coherence-transducer` gives, on each context, three
  trace-`1/4` sectors linked by partial unitaries whose off-diagonal blocks are
  exactly `(3/2)R_chi b R_psi`.  These are lossless local phase transports.
  `a4-coherence-fan-canonically-splits-multiplicity` strengthens this to an
  exact compiler: every local three-dimensional block is one fixed A4 qutrit
  tensored with one multiplicity wire.  The new
  `a4-canonical-coherence-data-hs-lipschitz` shows that all carrier projections
  and transports are uniformly HS-stable in the local generators.
- **External multiplicity is not a linear gluing obstruction.**
  `finite-subspace-gluing-is-amplification-stable` says that once the remaining
  coherence conditions are written as approximate membership in finitely many
  fixed base intertwiner subspaces, their Friedrichs-angle/spectral gluing
  constant survives tensor amplification unchanged.  Therefore the hard step
  is the nonlinear-to-linear extraction of those residuals, not the growing
  dimension `k_n` itself.
- **The packet sees the whole chart.**
  `atlas-a4-packet-letters-generate-both-a8-charts` proves by exact F2 closure
  that the ten distinct packet letters on either side generate all of A8; the
  two factors use the same ten-element set, whose directed word diameter is
  nine.  Consequently `atlas-a4-packet-commutant-synchronization` makes these
  ten letters a dimension-free commutant test for every regular amplification.
  A viable compiler now only has to extract from the A4 coherence network a
  bounded residual whose commutators with those packet letters are controlled
  by the holonomy/collision defect; finite averaging then rounds it into the
  global right-regular commutant.
- **Use bounded-depth carrier amplification.**
  The line carriers are explicit central idempotents and also satisfy
  `(PQP)^m=E+3^(-m)(P-E)`.  Thus any projection-valued synchronization
  argument can use a fixed polynomial depth chosen once to spend less than the
  numerical `1/128` budget, independently of `k_n`.
- **Collision 19243 is the frustration cycle.**
  The exact classical audit finds thirty automorphism alignments satisfying the
  A4 packet and zero surviving after adding `q_19243`.  That finite audit is
  discovery evidence, not the theorem: the required proof must show that the
  matrix-valued coherence fan cannot evade the same frustration by mixing
  multiplicity sectors.  The new generation/commutant facts rule out hiding in
  a packet-invisible chart subgroup, but do not by themselves convert the
  collision word into the needed commutator residual.
- **The abstract quotient is a bounded exact fork.**
  `atlas-a4-packet-collision-quotient-audit` packages the thirty pair-cubes and
  collision into one quotient of `A8*A8`.  If that quotient is finite, either a
  chart factor collapses (and finite-group HS stability proves this claim) or
  its regular representation is an explicit exact regular-margin nonclassical
  mode that the remaining Dirichlet estimate must beat.
