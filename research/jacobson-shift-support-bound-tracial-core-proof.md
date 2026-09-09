---
rg: 2
id: jacobson-shift-support-bound-tracial-core-proof
kind: route
title: Apply the uniform transvection support bound and simplicity to the compressed tracial model
target: jacobson-shift-surviving-head-has-a-tracial-core
requires:
  - uniform-finitary-support-makes-torsion-tracially-visible
  - binary-finitary-transvection-uniformly-controls-active-rank
  - jacobson-shift-head-generates-normal-finitary-kernel
  - jacobson-shift-head-dies-in-amenable-targets
artifacts:
  - research/artifacts/jacobson-surviving-head-has-a-tracial-core-2026-09-08.md
---

Section 5 of the artifact applies the generic theorem with `C=4`
to the standard finite intervals in the normal finitary kernel.
The involution has nonidentity eigenvalue `-1`, so active fraction
at least `1/4` gives normalized-Hilbert--Schmidt distance at least
one. Simplicity makes the new map injective on the whole kernel.
The earlier amenable-target proof establishes the exact centralizer
identity `C_Gamma(L)=ker(pi)`. Normal commutators put the new map's
kernel in that centralizer, giving the asserted second inclusion.
