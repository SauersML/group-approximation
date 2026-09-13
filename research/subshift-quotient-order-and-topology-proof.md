---
rg: 2
id: subshift-quotient-order-and-topology-proof
kind: route
title: Recover languages from relations and detect nonminimality by restriction kernels
target: binary-subshifts-embed-in-three-marked-kazhdan-groups
requires:
  - binary-subshift-language-has-quadratic-group-witnesses
  - unit-idempotent-elementary-group-has-three-torsion-generators
  - elementary-groups-over-fg-rings-have-property-t
  - simple-kazhdan-lef-group-from-minimal-subshift
artifacts:
  - research/artifacts/pestov91-marked-subshift-encoding-2026-09-13.md
---

Sections 1, 4 and 5 give the proof. The universal unit-idempotent ring
maps onto every binary subshift crossed product, yielding a fixed
three-generated Kazhdan source and uniform quotient Kazhdan constant.
Restriction gives marked epimorphisms for subshift inclusions, and the
language witnesses prove the converse. The finite window bound gives
continuity; injectivity and compactness give a closed topological image.

Infinite minimality gives simplicity and LEF by the base theorem over
`F_2`. A proper invariant subset produces a restriction epimorphism
with a nontrivial cylinder root in its kernel and nontrivial image.
A finite minimal orbit of length `N` has a finite matrix representation
killing `u^N-1`; its elementary root is nontrivial by the crossed-product
normal form. This excludes simplicity in the remaining case.
