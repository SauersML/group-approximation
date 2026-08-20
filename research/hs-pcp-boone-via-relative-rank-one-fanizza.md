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
`fanizza-final-bcs-has-fixed-nonlinear-menu` shows that its final flattening
uses only three nonlinear predicate shapes, while
`fanizza-fixed-nonlinear-menu-has-small-rank-gates` compiles all three into
fixed packets whose affine rank matrices have size at most twelve.  Every
violating atom creates one extra relative `M_2` multiplicity coordinate.
For the binary support subpacket the Laplacian gap is explicitly four; every
other fixed packet also has a positive dimension-independent finite-group gap.

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
