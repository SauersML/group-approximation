---
rg: 2
id: stw59-gauge-section-euler-image-proof
kind: route
title: The one-line gauge fibration has Euler image exactly n factorial times the integers
target: stw59-exact-factorial-unitary-component-groups
requires:
  - stw59-simple-ah-factorial-unitary-torsion
artifacts:
  - research/artifacts/stw59-exact-factorial-component-groups-2026-09-05.md
---

For rank r=n+sum d_j over a 2r-dimensional base, the gauge-to-unit-section
principal bundle has connected section space with fundamental group
H^(2r)(X;Z)=Z. Adding one line puts the total gauge group in the needed
stable range: pi0=K1(X)=0 and pi1=K0(X). Explicit local lifts and
complement rotations justify these identifications for the actual bundle.

The fundamental-group map is the top Euler/Chern number of a bundle
clutched over S2 times X. Its Chern-character formula has image contained
in n! Z; the sphere Bott class realizes exactly ±n!, proving equality.
The exact homotopy sequence therefore computes pi0 Gauge(E)=Z/(n!).
The previously proved exact-order unitary generates it. The explicit
tower preserves that generator, and norm approximation and finite-stage
path detection identify the entire limit component group.
