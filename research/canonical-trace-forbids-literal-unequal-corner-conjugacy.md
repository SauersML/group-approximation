---
rg: 2
id: canonical-trace-forbids-literal-unequal-corner-conjugacy
kind: route
title: Restrict the canonical group trace to the injected finite packet and use conjugacy invariance
target: literal-fiber-unequal-reflection-row-collapses-packet
requires:
  - one-coarse-to-fine-prefix-isometry-closes-the-reservoir
  - unitary-offdiagonal-block-gram-is-support-leakage
---

Injection of `H` identifies its group basis with distinct basis elements of
`G`; hence the canonical trace on `C[G]` restricts to the canonical trace on
`C[H]`.  Apply tracial invariance to `(LUR1)` to obtain `(LUR2)`.  Expanding
the two reflections in `(LUR3)` gives `W(1-2e)W^*=1-2f`, hence `WeW^*=f`.
The unequal coarse/fine traces contradict `(LUR2)` whenever `q` is nonzero.
