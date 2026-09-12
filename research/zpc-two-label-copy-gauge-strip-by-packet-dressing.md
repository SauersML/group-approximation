---
rg: 2
id: zpc-two-label-copy-gauge-strip-by-packet-dressing
kind: route
title: Lock the ZPC AND gauge by packet-dressed identity-label copies
target: zpc-controlled-pauli-and-hs-shared-gauge-lock
requires:
  - controlled-pauli-commutator-is-and-times-multiplicity-commutator
---

**REFUTED IN THE PACKET-DRESSING FORM.**  The proposed gauge strip was to
manufacture commuting-label copies of the controlled actors by multiplying
them by fixed Pauli-packet words, impose trivial commutator on those copies,
and reuse their multiplicity gauges in the active AND row.

`pauli-gauge-word-retains-and-cocycle`
proves that every dressed word whose gauge deletion is `[A,B]` retains the
quadratic `ab` Pauli cocycle, up to affine selector phases.  It therefore
cannot expose `I tensor [A,B]` simultaneously on all four sectors.  The
literal copies `XU,ZV` make the failure sharp: pairing their commutator with
the active one enforces XOR rather than excluding only the active-mismatch
sector.

Synchronizing a genuinely new identity-label copy by selector flips does not
repair the route.  By
`transitive-selector-flips-kill-leavitt-sibling-support`, any rank-preserving
orbit joining the forbidden `11` atom to an allowed atom propagates its zero
rank into allowed source mass; the maximal completeness-preserving orbit
separation leaves the forbidden gauge independent.  Thus this route is
invalidated for packet dressing and rank-preserving selector synchronization.
A non-rank-preserving, model-dependent mixed occurrence remains live.
