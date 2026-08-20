---
rg: 2
id: hs-pcp-boone-via-relative-rank-one-fanizza
kind: route
title: Feed the Fanizza polynomial recurrence through one fixed relative Pauli coordinate
target: hs-pcp-boone-compiler
requires:
  - relative-rank-one-fanizza-groupification
  - fanizza-turing-bcs-signal-collapse
  - fanizza-nonmember-signal-is-not-a-separated-mark
  - support-failure-packet-has-explicit-hs-payment
  - rank-one-no-signaling-pairing-floor
---

The cited Fanizza theorem supplies the finite Turing BCS, its polynomially
certified recurrence, and the final signal-versus-strategy-error collapse.
`support-failure-packet-has-explicit-hs-payment` compiles every forbidden
child-without-parent atom into one extra relative `M_2` multiplicity coordinate
inside a fixed 128-element group packet.  Its Laplacian gap is four, so any
extensive mismatch on that bit pays normalized-HS energy with no dimension
loss.

The only quantum mixing needed at this local endpoint is compatibility of
three pair laws on that single bit.  `rank-one-no-signaling-pairing-floor`
shows that shared endpoint marginals already force total failure at least one;
the rank-at-least-two counterboxes cannot hide the violation after the relative
bit has been exposed.

`relative-rank-one-fanizza-groupification` is exactly the remaining semantic
step: finitely present those packet transports without globally centralizing
the selectors, charge their failures by fixed relators, preserve the
polynomial/exponential Fanizza accounting, and connect a separate surviving
Boone mark to the initial carrier.  Its conclusion gives the constants and
two machine alternatives in `hs-pcp-boone-compiler`.  The existing route
`nonhyperlinear-from-hs-pcp-boone` then performs the self-referential final
step.
