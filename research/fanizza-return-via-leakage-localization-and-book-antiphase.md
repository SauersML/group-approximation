---
rg: 2
id: fanizza-return-via-leakage-localization-and-book-antiphase
kind: route
title: Close fixed-scale Fanizza return by localizing leakage and charging overlap with book antiphase
target: fixed-scale-contextual-multiplicity-holonomy
requires:
  - non-ce-bcs-has-robust-approximate-energy-gap
  - eight-slice-bookkeeping-symmetrizes-s3-failures
  - localized-non-ce-leakage-forces-cross-gram-overlap
  - shared-fanizza-exit-leakage-localization
  - three-book-hnn-antiphase-charges-every-cross-gram
  - positive-overlap-antiphase-closes-fanizza-return
---

Use the original shared-word energy for the robust BCS alternative.  The
eight-slice sources have surplus `q/16` over their parent capacity.  The
shared localization estimate charges off-capacity leakage, while the
multiple-HNN book tag charges the complete ordered overlap term.  Equation
`(PACF7)` gives the dimension-independent energy floor.

The HNN extension embeds the marked base, so exact completeness is algebraic
and does not require a tracial extension of the Fanizza witness.  This route
does not use the near-full scalar actuator `(SBO1)`, a spectral polar gauge,
or a recursive return amplifier.  Its only open input is the matrix-only
shared leakage localization `(SFEL2)`.
