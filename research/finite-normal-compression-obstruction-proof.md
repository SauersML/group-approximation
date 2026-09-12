---
rg: 2
id: finite-normal-compression-obstruction-proof
kind: route
title: Transport all compressors and cancel in a finite normal subgroup
target: finite-normal-compression-obstruction
requires: [kazhdan-asymptotic-commutant-transport]
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/ManuscriptExactWrappers.lean
  - GroupApproximation/Sofic/KazhdanAsymptoticCommutant.lean
---

## Why sufficient

Kazhdan transport sends the represented centralizer into the asymptotic
commutant after every word in one-sided compressors.  Thus every generator
of the compression defect tends to `1` in normalized Hilbert--Schmidt norm.
On a finite normal subgroup, conjugation permutes finitely many values; the
regular permutation action (equivalently finite-dimensional cancellation)
upgrades this convergence to exact triviality of the subgroup in every
corona representation.  The cited theorem formalizes the intrinsic defect
subgroup and the cancellation conclusion.
