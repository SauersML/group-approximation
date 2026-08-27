---
rg: 2
id: literal-sofic-via-amenable-kernel
kind: route
title: Prove literal soficity through its witness kernel
target: literal-group-sofic
requires: [sofic-non-mf-witness, literal-witness-kernel-amenable]
artifacts: [non_mf_groups_exist.tex]
---

## Why sufficient

The canonical map gives an exact sequence
`1 -> ker(E -> W) -> E -> W -> 1`.  The quotient `W` is sofic.  If the kernel
is amenable, extension permanence for sofic groups with amenable normal
subgroup makes `E` sofic.
