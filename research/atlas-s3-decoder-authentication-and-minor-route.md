---
rg: 2
id: atlas-s3-decoder-authentication-and-minor-route
kind: route
title: Authenticate the S4 extension triple, then invert the literal S3 channel minor
target: atlas-hard-packet-s3-channel-decoder
requires:
  - regular-chart-wedderburn-coefficient-compiler
  - s3-standard-operator-channel-has-fivefold-reduced-gauge
  - s3-hard-cell-three-channel-data-is-nondegenerate
  - actual-hard-prefix-generates-s4-over-raw-s3
  - separated-channel-identities-retain-rectangular-escape
  - atlas-hard-packet-authenticates-s4-extension-triple
  - atlas-mixed-minor-needs-nuisance-quotient-rank
  - atlas-authenticated-s3-extension-minor-decodes-pairings
---

The actual quotient-level hard-prefix `S4` is now available before the
decoder starts.  The Wedderburn compiler inserts its intrinsic central
projectors and exposes every operator block without choosing an external
multiplicity basis.  For a second `S4` extension it retains the cross-products
of the two canonical decompositions as noncommuting multiplicity variables.

Project the full named quotient relators through those blocks.  Retain every
extra multiplicity word as a nuisance column `D`.  The authentication claim
must put one extension-labelled triple on a common finite cut; the minor
claim must then yield scalar equations `C X+D Y=E` with

```text
rank [C D]=rank D+3.
```

Equivalently, `P_(ran D)^perp C` must have positive least singular value.
Only then may the nuisance-annihilating inverse estimate produce the three
defects `(S3D2)`.  A nonzero minor of `C` alone is not a certificate.

The separated rectangular no-go is an explicit falsification test: a carrier
determinant followed by an independent coefficient argument is not this
mixed system.
