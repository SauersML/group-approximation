---
rg: 2
id: projective-leavitt-unit-groups-mod-scalars-are-nonsofic
kind: claim
title: Over every finite field the binary Leavitt unit group modulo its scalars is nonsofic
distinct_from:
  d-ary-leavitt-groups-nonsofic-over-finite-fields: that is nonsoficity of the unit, GL and EL groups themselves; this is nonsoficity of their quotient by the finite central scalars, which no general permanence supplies and which here comes from an embedding of the unit group into the quotient.
  odd-leavitt-unit-groups-mod-scalars-are-fp-simple: that is finite presentability and simplicity of the same quotient; this is its nonsoficity.
artifacts:
  - research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md
---

For every finite field `k`, `L_k(1,2)^x / k^x` is not sofic. In particular
`PG = L_(F_3)(1,2)^x / {±1}`, the host of
`projective-ternary-leavitt-group-nonsurjunctive`, is nonsofic, so Gromov--Weiss
does not decide that root.

The argument does not pass nonsoficity through the finite central kernel. That
direction is not available in general. Instead, the quotient contains a copy of
the unit group (`leavitt-units-embed-in-their-scalar-quotient`), which is nonsofic
(`d-ary-leavitt-groups-nonsofic-over-finite-fields`), and soficity passes to
subgroups (`sofic-passes-to-subgroups`). Section 8 of the artifact.
