---
rg: 2
id: edgeful-or3-four-cap-link-closes-first-chord
kind: route
title: Use the zero-diagonal four-cap OR3 packet and authenticate its three parity repetitions
target: first-cycle-signed-hecke-chord
requires:
  - edgeful-or3-four-cap-walsh-packet
  - four-cap-common-phase-forces-trivial-mark
  - four-cap-two-chart-mixer-has-finite-clifford-evaluator
  - four-cap-three-actuator-hs-packet-blocker
  - edgeful-or3-coefficient-link-compiler
  - overlap-subdivision-preserves-coherent-piece-obstruction
---

The four-cap packet makes every root diagonal vanish, so the open compiler's
Fourier branch has only coefficient matchings.  It handles each unique
matching by a private eliminable pivot and handles the three repeated
matchings by authenticated sectorwise parity identities or by an actual
packet-injective coefficient link.  The surviving common phase keeps an
assignment projection outside the finite root packet.  These give the exact
chord identity while preserving the context PVMs and the earlier tree
overlaps, which is the first-cycle target.

Here “common phase” cannot mean one cap-independent literal word:
`four-cap-common-phase-forces-trivial-mark` proves that the three weight-two
cap parities would then force `J=1`.  Nor can it mean only a centrally
controlled sum, whose equations remain sectorwise.  The required
coefficient link must instead make a cap selector noncentral relative to a
second authenticated chart while preserving packet injectivity.

That condition is necessary but still not sufficient.
`four-cap-two-chart-mixer-has-finite-clifford-evaluator` constructs the
smallest marked selector mixer with noncommuting charts, embedded packet,
nontrivial central sign, and no packet retraction, yet evaluates the whole
cell in sixteen Clifford dimensions while remaining faithful on the packet.
The required link must therefore escape every packet-preserving finite
evaluation, not merely charge one selector commutator by `J`.

The exact version of that escape is now available:
`four-cap-three-actuator-destroys-all-fd-packet-evaluations` amalgamates the
cross-chart D8 seed with the affine-Leavitt active root and preserves the
packet by normal forms while killing `J` in every finite-dimensional
representation.  Its normalized-HS use is exactly
`four-cap-three-actuator-hs-packet-blocker`, whose only analytic hole is the
existing affine-Leavitt root-to-coefficient decoder.  Thus this route no
longer treats exact packet-retraction destruction as the missing theorem.

The subdivision audit rules out treating macro girth as a substitute for
the required cap-sector/link certificate.
