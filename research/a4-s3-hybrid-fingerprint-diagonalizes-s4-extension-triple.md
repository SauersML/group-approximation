---
rg: 2
id: a4-s3-hybrid-fingerprint-diagonalizes-s4-extension-triple
kind: claim
title: The joint A4-line and S3-scalar fingerprint diagonalizes the three ambiguous S4 extensions
distinct_from:
  s3-hard-cell-three-channel-data-is-nondegenerate: that uses all three S3 restriction rows or the standard-channel Racah transform; this replaces the ambiguous standard row by one A4 line row and obtains a diagonal fingerprint.
  regular-subgroup-branching-is-hall-balanced: that rules out a Hall deficit from one restriction graph; this uses two transverse subgroup restrictions only to label three extension coordinates, not to derive a dimension deficit.
  atlas-hard-packet-authenticates-s4-extension-triple: that must realize the fingerprint with literal packet words on one common finite cut; this is the exact finite representation-theoretic calculation it may use.
---

Let `A4` be the alternating subgroup of `S4` and let `S3` be a point
stabilizer.  Write `omega,omega^2` for the two nontrivial one-dimensional
characters of `A4`, `tau` for its three-dimensional irreducible, and
`1,epsilon,sigma` for the irreducibles of `S3`.  For the three `S4` types
which meet in the standard `S3` channel, restriction gives

```text
Res^S4_A4(2)          = omega + omega^2,
Res^S4_A4(3)          = tau,
Res^S4_A4(3 epsilon)  = tau,                           (HFP1)

Res^S4_S3(2)          = sigma,
Res^S4_S3(3)          = 1 + sigma,
Res^S4_S3(3 epsilon)  = epsilon + sigma.              (HFP2)
```

Consequently the three measurements

```text
m_(A4,omega),       m_(S3,1),       m_(S3,epsilon)     (HFP3)
```

on extension multiplicities `(x_2,x_3,x_(3 epsilon))` have coefficient
matrix

```text
H = [ 1 0 0 ]
    [ 0 1 0 ]
    [ 0 0 1 ].                                        (HFP4)
```

The same holds with `omega^2` in the first row.  Thus a single nontrivial
`A4` line channel distinguishes type `2` from the two three-dimensional
extensions, and the trivial/sign scalar channels of `S3` distinguish the
remaining pair.  No standard `S3` measurement is required for this
authentication step.

This is useful specifically because the `A4` line carrier is a fixed central
idempotent by `a4-line-carriers-explicit-idempotents`, while the troublesome
fivefold gauge of `s3-standard-operator-channel-has-fivefold-reduced-gauge`
lives in the standard **operator** channel.  The calculation does not itself
assert that an arbitrary atlas microstate contains an `S4` representation.
It says that if the literal hard packet couples these three word-visible
subgroup projections on one relative transport, the extension labels are
already authenticated before any standard-channel recoupling is attempted.

