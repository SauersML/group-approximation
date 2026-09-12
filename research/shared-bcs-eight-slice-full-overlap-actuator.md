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
ordinary word traces.  This permits a matrix-ultraproduct separation or a
packet-compressed Toeplitz decoder without first constructing block maps.
However `universal-tracial-certificates-cannot-force-eight-slice-overlap`
rules out an ordinary cyclic SOS, a finite positive-definite Hecke inequality,
or a finite-level NPA dual: each would also hold in the canonical regular
trace, where the overlap deficit is `tau(P_f)/16`.  The certificate must be a
genuine Connes-embedding separator.  In particular it must consume
cross-context moments of the same shared selector words whose non-CE profile
supplies the finite-dimensional gap; a certificate depending only on scalar
forbidden masses is invalid.

`eight-slice-overlap-requires-a-connes-embedding-separator` records the
positive form of this firewall: the desired inequality is already the final
matrix-versus-regular trace separation, not a purely finite-packet lemma.

There is now a concrete finite source-specific candidate moment object:
`localized-non-ce-leakage-forces-cross-gram-overlap` forms the Gram matrix of
`L`, `Z_xL`, `LZ_x`, and `R(Z)L` on every off-capacity leakage projection.
The corner-localized non-CE gap forces its positive functional `Lambda` to be
at least `beta tau(L)` in matrices.  Combined with Gram capacity, small
`Lambda` forces positive cross-Gram overlap, while source-only moments admit
an exact orthogonal-coordinate countermodel.  To reach the full-overlap form
`(SBO1)`, the actuator must still turn that positive spectral overlap into the
single returned `S`-to-`C` compression; the universal packet relations do not
do so.
