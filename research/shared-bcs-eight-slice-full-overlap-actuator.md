---
rg: 2
id: shared-bcs-eight-slice-full-overlap-actuator
kind: claim
title: One shared-word actuator returns the equalized failure sum with full scalar overlap
distinct_from:
  shared-bcs-eight-slice-symmetric-return: that asks for three source partial isometries and a full leakage/cross-Gram estimate; this asks only for one scalar moment lower bound.
  schur-reynolds-one-overlap-actuator: that acts on adjoint Reynolds ranges and pays a quadratic forbidden-density gap; this acts on the ordinary eight-slice failure carrier and pays linearly.
  exact-five-fourths-projection-return-collapses-the-packet: that forbids a universal exact projection return; this requires the overlap estimate only for finite matrix microstates and allows it to fail in the regular representation.
---

OPEN.  Construct one finitely presented marked extension of the fixed shared
non-CE BCS and one actuator word `W` (or one fixed packet-compressed unitary
decoded from finitely many actuator words) such that, after simultaneous
fixed-packet exactification, the projections `S,C` of `(EOM1)--(EOM2)` obey

```text
tau(S W^* C W S)
 >= tau(S)-K E_rel-o(1)                                (SBO1)
```

in every finite-dimensional marked microstate.  Here `E_rel` is a
bounded-overlap energy in the original shared BCS words, formed before the
context occurrences are separated, and `K` is independent of matrix
dimension.

The exact marked HALT representation need only extend after countable
amplification.  Its actuator may implement a Hilbert-hotel inclusion between
infinite multiplicity spaces; no tracial extension is required.  The group
relations themselves must remain consistent with the canonical regular
representation, where `(SBO1)` is allowed to fail.

By `(EOM7)`, the decoder target is one finite rational combination of fixed
ordinary word traces.  This makes a direct Hecke/positive-definite, NPA-dual,
or packet-compressed Toeplitz certificate possible without first constructing
block maps.  A certificate depending only on the scalar forbidden masses is
invalid; it must consume cross-context moments of the same shared selector
words whose non-CE profile supplies the robust BCS gap.
