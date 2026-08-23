---
rg: 2
id: regular-congruence-padding-weil-boundary-proof
kind: route
title: Compare one native Weil line with one full regular congruence packet
target: regular-padding-is-not-small-on-weil-boundaries
requires:
  - even-weil-fixed-line-compression
  - bs14-native-cells-cross-every-length-cutoff
---

The first dependency supplies the dimension `(RCW1)`, exact
same-dimensional nonextension, and the one-line native completion.  The
second supplies the length-one source, unbounded exit orbit, and order-one
cross-cutoff coupling.  If padding is restricted to regular `Q_p` packets,
same-dimensional nonextension forces at least one packet.  Formula `(RCW2)`
and division by `(RCW1)` give `(RCW3)` exactly.  Since the source length is
one independently of `p`, no slowly growing short-orbit cutoff changes this
calculation.
