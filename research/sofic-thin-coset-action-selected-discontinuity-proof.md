---
rg: 2
id: sofic-thin-coset-action-selected-discontinuity-proof
kind: route
title: Embed the thin free coset wreath product and retain its quasiregular lamp orbit
target: sofic-thin-coset-action-refutes-selected-profinite-continuity
requires:
  - centralizer-hnn-is-free-generalized-wreath
  - gkp-free-wreath-permanence
  - thin-hnn-regular-selected-module-is-profinite-discontinuous
---

The actor `A` and lamp group `Z` are sofic.  If
`A curvearrowright A/C` is sofic, `gkp-free-wreath-permanence` and
`centralizer-hnn-is-free-generalized-wreath` make

```text
G=<A,t | [t,C]=1>
```

sofic.  Its canonical group character consequently embeds into a tracial
matrix ultraproduct.  The embedded stable letter remains `C`-central, and
all of its mixed conjugation moments remain the canonical ones.  By
`thin-hnn-regular-selected-module-is-profinite-discontinuous`, the selected
cyclic module is `lambda_(A/C)` and is not weakly contained in `pi_FD^0`.
This is the required matrix-origin failure of selected profinite
continuity.
