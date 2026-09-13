---
rg: 2
id: simple-kazhdan-universal-locally-finite-host-proof
kind: route
title: Choose a universal odometer factor in the characteristic-two subshift construction
target: simple-kazhdan-lef-hosts-all-countable-locally-finite
requires:
  - simple-kazhdan-lef-group-from-minimal-subshift
  - minimal-binary-subshift-has-universal-odometer-factor
  - odometer-matrix-towers-host-locally-finite-groups
  - binary-pestov-groups-are-three-torsion-generated
artifacts:
  - research/artifacts/pestov91-universal-locally-finite-host-2026-09-13.md
  - research/artifacts/pestov91-three-torsion-generators-2026-09-13.md
---

Choose the binary subshift from the factor input and work over `F_2`.
The existing subshift theorem makes `EL_3(R)` infinite, Kazhdan and LEF,
and simple modulo its centre. That centre lies in `F_2^times I_3`, hence
is trivial. The matrix-tower input embeds every countable locally finite
group in this same fixed group.

The three-torsion-generator input applies to this same binary subshift
and gives the explicit triple of orders `7,2,2`, improving the earlier
eighteen-involution bound. Its decoder proof recovers the cylinder
idempotent and shift coefficients from these matrices. Infinite simplicity excludes
finite quotients; finite presentation plus LEF would force residual
finiteness, so the host is not finitely presented. The stated examples
are countable locally finite groups. LEF supplies the approximation
consequences by finite regular permutation models.
