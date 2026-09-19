---
rg: 2
id: one-hecke-overlap-saturation-proves-iwahori-transfer
kind: route
title: Convert saturation of each projection compression into second-vertex commutation
target: canonical-iwahori-projection-commutant-transfer
requires:
  - canonical-iwahori-one-hecke-overlap-saturates
---

For each fixed second-vertex generator, `(IOS5)` gives

```text
||[p_n,U_n]||_2^2
 =2(tr(p_n)-tr(p_nU_np_nU_n^*)).
```

The prerequisite makes the right-hand side tend to zero.  Taking the
maximum over the fixed finite generating set proves `(CIP3)`.  Conversely
`(CIP3)` implies `(COH1)` by the same identity, so the scalar terminal is an
equivalent one-overlap formulation rather than a strengthening.
