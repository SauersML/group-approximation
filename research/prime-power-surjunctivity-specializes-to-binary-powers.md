---
rg: 2
id: prime-power-surjunctivity-specializes-to-binary-powers
kind: route
title: The prime-power statement at p = 2 is the binary-power statement
target: stable-finiteness-forces-binary-surjunctivity
requires:
  - stable-finiteness-forces-prime-power-surjunctivity
artifacts:
  - research/artifacts/formalizability-prime-fields-and-alphabet-bridge-2026-09-12.md
---

Instantiate the prerequisite at `p = 2`. Its hypothesis is stable finiteness of `F_2[G]` and its conclusion
is surjunctivity over every alphabet of size `2^n`, which is the target. This route and
`formalizable-pairs-reduce-surjunctivity-to-kaplansky` are two independent ways into the target: this one
passes through stable formalizability, that one through unstabilized binary formalizability.
