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
  - atlas-hard-packet-authenticates-s4-extension-triple
  - atlas-authenticated-s3-extension-minor-decodes-pairings
---

The Wedderburn compiler exposes every operator block without choosing an
external-multiplicity basis.  The fivefold-gauge calculation fixes the full
standard-channel search space and prevents the Racah triple from being
mistaken for the whole operator channel.  The authentication claim uses
literal packet relations to select the extension-labelled triple on one
common finite cut.  The minor claim then applies the established exact
three-channel transforms to the actual projected rows and solves for the
three defects `(S3D2)` with a fixed inverse-matrix constant.
