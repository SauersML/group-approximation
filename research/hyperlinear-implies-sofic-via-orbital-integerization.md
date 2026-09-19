---
rg: 2
id: hyperlinear-implies-sofic-via-orbital-integerization
kind: route
title: Round the pair-space commutant to a coherent configuration, then to an action
target: hyperlinear-implies-sofic
requires:
  - coherent-configuration-orbital-rounding
  - balanced-replica-hs-amplification
---

The intermediate-category route: unitary representation → approximately
coherent orbital algebra → finite relational model → permutation action.

Given a hyperlinear microstate of a finite window, apply balanced doubling
`U ↦ U ⊗ conj(U)` and replication.  By
`balanced-replica-hs-amplification` this preserves the small multiplicative
defect (at cost `sqrt(2m)`) and sharpens the trace separation to
`|tau(U_w)|^{2m}`; structurally it is the passage to the pair space, which on
the permutation side is the action on ordered pairs — so the amplified data is
of exactly the type an orbital analysis consumes.  By
`coherent-configuration-orbital-rounding` the pair-space commutant then carries
a positive, approximately disjoint family whose structure constants are within
`o(1)` of nonnegative integers; rounding them exactly gives a finite coherent
configuration compatible with the generator action, and its relational model
yields the permutation model of the window.

The last step is the route's exposed flank: a coherent configuration need not
be schurian, so "yields the permutation model" is where a proof must either
verify schurity for the configurations this construction produces, or work with
the relational model directly and show it already gives a sofic approximation.
That is stated in the premise's body as the known obstruction, and it is the
first thing to attack if the rounding half ever succeeds.
